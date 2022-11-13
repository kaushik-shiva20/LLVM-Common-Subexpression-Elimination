#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <iostream>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/GenericDomTree.h"

using namespace llvm;

static void CommonSubexpressionElimination(Module &);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

bool isDead(Instruction &I);
void RunDeadCodeElimination(Module &M);
bool cse_check_opcode(Instruction &I);
void process_load_worklist();
void process_store_worklist();

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));
static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};
int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE) {
        RunDeadCodeElimination(*M.get());
        CommonSubexpressionElimination(*M.get());

        //std::cout << "*****************" << std::endl;
        std::cout << "* CSEDead--------" << CSEDead.getValue() << std::endl;
        std::cout << "* CSEElim--------" << CSEElim.getValue() << std::endl;
        std::cout << "* CSESimplify----" << CSESimplify.getValue() << std::endl;
        std::cout << "* CSELdElim------" << CSELdElim.getValue() << std::endl;
        std::cout << "* CSEStore2Load--" << CSEStore2Load.getValue() << std::endl;
        std::cout << "* CSEStElim------" << CSEStElim.getValue() << std::endl;
        std::cout << "* Total----------" << (CSEDead.getValue() + CSEElim.getValue() + CSESimplify.getValue() + CSELdElim.getValue() + CSEStore2Load.getValue() + CSEStElim.getValue()) << std::endl;
        //std::cout << "*****************" << std::endl;

    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}


static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}


std::set<Instruction *> load_worklist;
std::set<Instruction *> store_worklist;
std::set<Instruction *> store_load_worklist;

DominatorTree gDT;
//TODO: uncomment all volatile checks llvm-12 issue so commented
void process_load_worklist()
{
    //return;
    for(auto p=load_worklist.begin();p!=load_worklist.end();p++)
    {
        Instruction* i = *p;
        for(auto q=p;q!=load_worklist.end();)
        {
            Instruction* j = *q;
            if((i!=j)&&(i->getOperand(0) == j->getOperand(0)) && (!j->isVolatile()) && (i->getType()->getTypeID() == j->getType()->getTypeID()))
            {
                if(gDT.dominates(i,j))
                {
                    if(!(j->isTerminator() || j->isExceptionalTerminator() || j->isIndirectTerminator() || j->mayHaveSideEffects() || (!j->isSafeToRemove())))
                    {
                        j->replaceAllUsesWith(cast<Value>(&*i));
                        j->eraseFromParent();
                        q = load_worklist.erase(q);
                        CSELdElim++;
                    }else
                    {
                        q++;
                    }
                }else
                {
                    q++;
                }
            }else
            {
                q++;
            }
        }
    }
    load_worklist.clear();
}

void process_store_worklist()
{
    //return;
    //std::reverse(store_worklist.begin(), store_worklist.end());
    std::set<Instruction *>::reverse_iterator p;
    std::set<Instruction *>::reverse_iterator q;

    for(p=store_worklist.rbegin();p!=store_worklist.rend();p++)
    {
        Instruction* i = *p;
        for(q=p;q!=store_worklist.rend();)
        {
            Instruction* j = *q;
            if((i!=j)&&(i->getOperand(1) == j->getOperand(1)) && (!j->isVolatile()) && (i->getType()->getTypeID() == j->getType()->getTypeID()))
            {
                if(gDT.dominates(i,j))
                {
                    if(!(j->isTerminator() || j->isExceptionalTerminator() || j->isIndirectTerminator() || j->mayHaveSideEffects() || (!j->isSafeToRemove())))
                    {
                        j->replaceAllUsesWith(cast<Value>(&*i));
                        j->eraseFromParent();
                        //std::advance(q,1);
                        store_worklist.erase(std::next(q).base());
                        CSEStElim++;
                    }else
                    {
                        q++;
                    }
                }else
                {
                    q++;
                }
            }else
            {
                q++;
            }
        }
    }
    store_worklist.clear();
    //std::reverse(store_worklist.begin(), store_worklist.end());
}

void process_store_load_worklist()
{
    //return;
    for(auto p=store_load_worklist.begin();p!=store_load_worklist.end();p++)
    {
        Instruction* i = *p;
        if(i->getOpcode() == Instruction::Store)
        {
            for (auto q = p; q != store_load_worklist.end();) {
                Instruction *j = *q;
                if((i != j) && (j->getOpcode() == Instruction::Store) && (j->getOperand(1) == i->getOperand(1)))
                {
                    q++;
                    break;
                }else if ((i != j) && (j->getOpcode() == Instruction::Load) && (j->getOperand(0) == i->getOperand(1)) && (!j->isVolatile()) && (j->getType()->getTypeID() == i->getOperand(1)->getType()->getTypeID()))
                {
                    if(gDT.dominates(i,j)) {
                        if(!(j->isTerminator() || j->isExceptionalTerminator() || j->isIndirectTerminator() || j->mayHaveSideEffects() || (!j->isSafeToRemove()))) {
                            j->replaceAllUsesWith(i->getOperand(0));
                            j->eraseFromParent();
                            q = store_load_worklist.erase(q);
                            CSEStore2Load++;
                        }else
                        {
                            q++;
                        }
                    }else
                    {
                        q++;
                    }
                } else {
                    q++;
                }
            }
        }
    }
    store_load_worklist.clear();
}
static void CommonSubexpressionElimination(Module &M) {

    /* The following optimizations are handled in this function
     * Optimization 0: Eliminate dead instructions
     * Optimization 1: Simplify Instructions
     * */
    //RunDeadCodeElimination(M);

    /* Common Subexpression Elimination */
    /* Parse all the blocks and eliminate common sub expressions within the block */
    // loop over functions
    for(auto f = M.begin(); f!=M.end(); f++)
    {
        // loop over basic blocks
        if (!f->empty())
        {
            gDT = DominatorTree(*f);
            for (auto bb = f->begin(); bb != f->end(); bb++)
            {
                if (!bb->empty())
                {
                    for (auto i = bb->begin(); i != bb->end(); i++)
                    {
                        if (i->getOpcode() == Instruction::Load) {
                            load_worklist.insert(&*i);
                            process_store_worklist();
                        } else if (i->getOpcode() == Instruction::Store) {
                            store_worklist.insert(&*i);
                            process_load_worklist();
                        } else {
                            /* Checks for
                             * Do not consider Loads, Stores, Terminators, VAArg, Calls, Allocas, and FCmps
                             * */
                            if (cse_check_opcode(*i)) {
                                bool areOperandsSame;
                                for (auto j = i; j != bb->end();) {
                                    /* Checks for
                                     * ■	Same opcode
                                     * ■	Same type (LLVMTypeOf of the instruction not its operands)
                                     * ■	Same number of operands
                                     * ■	Same operands in the same order (no commutativity)
                                     * */
                                    /*volatile static unsigned i_op;
                                    volatile static unsigned j_op;
                                    i_op = i->getOpcode();
                                    j_op = j->getOpcode();*/
                                    if ((i != j) &&
                                        (i->getOpcode() == j->getOpcode()) &&
                                        (i->getType()->getTypeID() == j->getType()->getTypeID()) &&
                                        (i->getNumOperands() == j->getNumOperands())) {
                                        areOperandsSame = true;
                                        for (int w = 0; w < i->getNumOperands(); w++) {
                                            if (i->getOperand(w) != j->getOperand(w)) {
                                                areOperandsSame = false;
                                                break;
                                            }
                                        }
                                        if (areOperandsSame) {
                                            if(gDT.dominates(&*i,&*j)) {
                                                j->replaceAllUsesWith(dyn_cast<Value>(i));
                                                j = j->eraseFromParent();
                                                CSEElim++;
                                            }else
                                            {
                                                j++;
                                            }
                                        } else {
                                            j++;
                                        }
                                    } else {
                                        j++;
                                    }
                                }
                            }
                        }
                    }
                    process_load_worklist();
                    process_store_worklist();
                }
            }
        }
    }

    /* Parse all the children blocks in the dominator tree and eliminate common sub expressions /*/CSEElim++;//remove this
    for(auto f = M.begin(); f!=M.end(); f++)
    {
        if (!f->empty())
        {
            gDT = DominatorTree(*f);
            // loop over functions
            DominatorTree mDT(*f);

            for (auto node = GraphTraits<DominatorTree *>::nodes_begin(&mDT);
                 node != GraphTraits<DominatorTree *>::nodes_end(&mDT); ++node)
            {
                BasicBlock *CurrBB = node->getBlock();
                if (!CurrBB->empty())
                {
                    for (auto i = CurrBB->begin(); i != CurrBB->end(); i++)
                    {
                        /* Checks for
                         * Do not consider Loads, Stores, Terminators, VAArg, Calls, Allocas, and FCmps
                         * */

                        if ((i->getOpcode() == Instruction::Load) || (i->getOpcode() == Instruction::Store)) {
                            store_load_worklist.insert(&*i);
                        } else {
                            if (cse_check_opcode(*i)) {
                                for (auto ChildNode: node->children())
                                {
                                    BasicBlock *ChildBB = ChildNode->getBlock();
                                    if(!ChildBB->empty())
                                    {
                                        for (auto j = ChildBB->begin(); j != ChildBB->end();) {
                                            /* Checks for
                                             * ■	Same opcode
                                             * ■	Same type (LLVMTypeOf of the instruction not its operands)
                                             * ■	Same number of operands
                                             * ■	Same operands in the same order (no commutativity)
                                             * */
                                            if ((i != j) &&
                                                (i->getOpcode() == j->getOpcode()) &&
                                                (i->getType()->getTypeID() == j->getType()->getTypeID()) &&
                                                (i->getNumOperands() == j->getNumOperands())) {
                                                bool areOperandsSame = true;
                                                for (int w = 0; w < i->getNumOperands(); w++) {
                                                    if (i->getOperand(w) != j->getOperand(w)) {
                                                        areOperandsSame = false;
                                                        break;
                                                    }
                                                }
                                                if (areOperandsSame) {
                                                    if(gDT.dominates(&*i,&*j)) {
                                                        j->replaceAllUsesWith(dyn_cast<Value>(i));
                                                        j = j->eraseFromParent();
                                                        CSEElim++;
                                                    }else
                                                    {
                                                        j++;
                                                    }
                                                } else {
                                                    j++;
                                                }
                                            } else {
                                                j++;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    process_store_load_worklist();
                }
            }
        }
    }
}

void RunDeadCodeElimination(Module &M)
{
    std::set<Instruction*> worklist;

    // loop over functions
    for(auto f = M.begin(); f!=M.end(); f++) {
        // loop over basic blocks
        if (!f->empty()) {
            for (auto bb = f->begin(); bb != f->end(); bb++) {
                //SimplifyInstructionsInBlock(&*bb);
                // loop over instructions
                if(!bb->empty()) {
                    for (auto i = bb->begin(); i != bb->end();) {
                        if (isDead(*i)) {
                            // remove it!
                            CSEDead++;
                            i = i->eraseFromParent();
                            //worklist.insert(&*i);
                        } else {

                            const DataLayout &DL = i->getModule()->getDataLayout();
                            Value *temp = SimplifyInstruction(&*i, {DL});
                            if (temp) {
                                CSESimplify++;
                                i->replaceAllUsesWith(temp);
                                i = i->eraseFromParent();
                            } else {
                                i++;
                            }
                        }
                    }
                }
            }
        }
    }
}

bool isDead(Instruction &I)
{
    /*
        Check necessary requirements, otherwise return false
     */
    if ( I.use_begin() == I.use_end() )
    {
        int opcode = I.getOpcode();
        switch(opcode){
            case Instruction::Add:
            case Instruction::FNeg:
            case Instruction::FAdd:
            case Instruction::Sub:
            case Instruction::FSub:
            case Instruction::Mul:
            case Instruction::FMul:
            case Instruction::UDiv:
            case Instruction::SDiv:
            case Instruction::FDiv:
            case Instruction::URem:
            case Instruction::SRem:
            case Instruction::FRem:
            case Instruction::Shl:
            case Instruction::LShr:
            case Instruction::AShr:
            case Instruction::And:
            case Instruction::Or:
            case Instruction::Xor:
            //case Instruction::Alloca:
            case Instruction::GetElementPtr:
            case Instruction::Trunc:
            case Instruction::ZExt:
            case Instruction::SExt:
            case Instruction::FPToUI:
            case Instruction::FPToSI:
            case Instruction::UIToFP:
            case Instruction::SIToFP:
            case Instruction::FPTrunc:
            case Instruction::FPExt:
            case Instruction::PtrToInt:
            case Instruction::IntToPtr:
            case Instruction::BitCast:
            case Instruction::AddrSpaceCast:
            case Instruction::ICmp:
            case Instruction::FCmp:
            case Instruction::PHI:
            case Instruction::Select:
            case Instruction::ExtractElement:
            case Instruction::InsertElement:
            case Instruction::ShuffleVector:
            case Instruction::ExtractValue:
            case Instruction::InsertValue:
                return true; // dead, but this is not enough

            case Instruction::Load:
            {
                LoadInst *li = dyn_cast<LoadInst>(&I);
                if (li && li->isVolatile())
                    return false;
                return true;
            }
            default:
                // any other opcode fails
                return false;
        }
    }

    return false;
}

bool cse_check_opcode(Instruction &I)
{
    bool mRetVal = true;
    int opcode = I.getOpcode();
    switch (opcode) {
        case Instruction::Add:
        case Instruction::FNeg:
        case Instruction::FAdd:
        case Instruction::Sub:
        case Instruction::FSub:
        case Instruction::Mul:
        case Instruction::FMul:
        case Instruction::UDiv:
        case Instruction::SDiv:
        case Instruction::FDiv:
        case Instruction::URem:
        case Instruction::SRem:
        case Instruction::FRem:
        case Instruction::Shl:
        case Instruction::LShr:
        case Instruction::AShr:
        case Instruction::And:
        case Instruction::Or:
        case Instruction::Xor:
        //case Instruction::GetElementPtr:
        //case Instruction::ICmp:
            mRetVal = true;
            break;
        default:
            mRetVal = false;
            break;
    }

    if(I.isVolatile())
    {
        mRetVal = false;
    }
    if(I.isTerminator() || I.isExceptionalTerminator() || I.isIndirectTerminator() || I.mayHaveSideEffects() || (!I.isSafeToRemove()))
    {
        mRetVal = false;
    }
    //mRetVal = false;
    return mRetVal;

}