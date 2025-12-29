/**
 * AEMgr.cpp
 * @author kisslune 
 */

#include "AELib.h"
#include "Util/Options.h"
#include "Util/WorkList.h"

using namespace SVF;
using namespace SVFUtil;

/// Abstract state updates on an AddrStmt
void AbstractExecution::updateStateOnAddr(const AddrStmt *addr)
{
    const ICFGNode *node = addr->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    as.initObjVar(SVFUtil::cast<ObjVar>(addr->getRHSVar()));
    as[addr->getLHSVarID()] = as[addr->getRHSVarID()];
}


void AbstractExecution::updateStateOnCopy(const CopyStmt *copy)
{
    const ICFGNode *node = copy->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    auto lhs = copy->getLHSVarID();
    auto rhs = copy->getRHSVarID();
    // TODO: your code starts from here
    auto getZExtValue = [](AbstractState &as, const SVFVar *var) {
        const SVFType *type = var->getType();
        if (SVFUtil::isa<SVFIntegerType>(type))
        {
            u32_t bits = type->getByteSize() * 8;
            if (as[var->getId()].getInterval().is_numeral())
            {
                if (bits == 8)
                {
                    int8_t signed_i8_value = as[var->getId()].getInterval().getIntNumeral();
                    u32_t unsigned_value = static_cast<uint8_t>(signed_i8_value);
                    return IntervalValue(unsigned_value, unsigned_value);
                }
                else if (bits == 16)
                {
                    s16_t signed_i16_value = as[var->getId()].getInterval().getIntNumeral();
                    u32_t unsigned_value = static_cast<u16_t>(signed_i16_value);
                    return IntervalValue(unsigned_value, unsigned_value);
                }
                else if (bits == 32)
                {
                    s32_t signed_i32_value = as[var->getId()].getInterval().getIntNumeral();
                    u32_t unsigned_value = static_cast<u32_t>(signed_i32_value);
                    return IntervalValue(unsigned_value, unsigned_value);
                }
                else if (bits == 64)
                {
                    s64_t signed_i64_value = as[var->getId()].getInterval().getIntNumeral();
                    return IntervalValue((s64_t) signed_i64_value, (s64_t) signed_i64_value);
                }
                else
                    assert(false && "cannot support int type other than u8/16/32/64");
            }
            else
            {
                return IntervalValue::top();
            }
        }
        return IntervalValue::top();
    };
    auto getTruncValue = [&](const AbstractState &as, const SVFVar *var, const SVFType *dstType) {
        const IntervalValue &itv = as[var->getId()].getInterval();
        if (itv.isBottom())
            return itv;
        s64_t int_lb = itv.lb().getIntNumeral();
        s64_t int_ub = itv.ub().getIntNumeral();
        u32_t dst_bits = dstType->getByteSize() * 8;
        if (dst_bits == 8)
        {
            int8_t s8_lb = static_cast<int8_t>(int_lb);
            int8_t s8_ub = static_cast<int8_t>(int_ub);
            if (s8_lb > s8_ub)
            {
                return IntervalValue(INT8_MIN, INT8_MAX);
            }
            return IntervalValue(s8_lb, s8_ub);
        }
        else if (dst_bits == 16)
        {
            s16_t s16_lb = static_cast<s16_t>(int_lb);
            s16_t s16_ub = static_cast<s16_t>(int_ub);
            if (s16_lb > s16_ub)
            {
                return IntervalValue(INT16_MIN, INT16_MAX);
            }
            return IntervalValue(s16_lb, s16_ub);
        }
        else if (dst_bits == 32)
        {
            s32_t s32_lb = static_cast<s32_t>(int_lb);
            s32_t s32_ub = static_cast<s32_t>(int_ub);
            if (s32_lb > s32_ub)
            {
                return IntervalValue(INT32_MIN, INT32_MAX);
            }
            return IntervalValue(s32_lb, s32_ub);
        }
        else
        {
            assert(false && "cannot support dst int type other than u8/16/32");
            abort();
        }
    };

    if (copy->getCopyKind() == CopyStmt::COPYVAL)
    {
        as[lhs] = as[rhs];
    }
    else if (copy->getCopyKind() == CopyStmt::ZEXT)
    {
        as[lhs] = getZExtValue(as, copy->getRHSVar());
    }
    else if (copy->getCopyKind() == CopyStmt::SEXT)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::FPTOSI)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::FPTOUI)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::SITOFP)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::UITOFP)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::TRUNC)
    {
        as[lhs] = getTruncValue(as, copy->getRHSVar(), copy->getLHSVar()->getType());
    }
    else if (copy->getCopyKind() == CopyStmt::FPTRUNC)
    {
        as[lhs] = as[rhs].getInterval();
    }
    else if (copy->getCopyKind() == CopyStmt::INTTOPTR)
    {
        // insert nullptr
    }
    else if (copy->getCopyKind() == CopyStmt::PTRTOINT)
    {
        as[lhs] = IntervalValue::top();
    }
    else if (copy->getCopyKind() == CopyStmt::BITCAST)
    {
        if (as[rhs].isAddr())
        {
            as[lhs] = as[rhs];
        }
        else
        {
            // do nothing
        }
    }
    else
        assert(false && "undefined copy kind");
}


void AbstractExecution::updateStateOnStore(const StoreStmt *store)
{
    const ICFGNode *node = store->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    auto lhs = store->getLHSVarID();
    auto rhs = store->getRHSVarID();
    // TODO: your code starts from here
    as.storeValue(lhs, as[rhs]);
}


void AbstractExecution::updateStateOnLoad(const LoadStmt *load)
{
    const ICFGNode *node = load->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    auto lhs = load->getLHSVarID();
    auto rhs = load->getRHSVarID();
    // TODO: your code starts from here
    as[lhs] = as.loadValue(rhs);
}


void AbstractExecution::updateStateOnGep(const GepStmt *gep)
{
    AbstractState &as = getAbsStateFromTrace(gep->getICFGNode());
    u32_t rhs = gep->getRHSVarID();
    u32_t lhs = gep->getLHSVarID();
    // TODO: your code starts from here
    IntervalValue offsetPair = as.getElementIndex(gep);
    APOffset lb = offsetPair.lb().getIntNumeral() < Options::MaxFieldLimit()
                  ? offsetPair.lb().getIntNumeral()
                  : Options::MaxFieldLimit();
    APOffset ub = offsetPair.ub().getIntNumeral() < Options::MaxFieldLimit()
                  ? offsetPair.ub().getIntNumeral()
                  : Options::MaxFieldLimit();
    AbstractValue gepAddrs;
    for (APOffset i = lb; i <= ub; i++)
        gepAddrs.join_with(as.getGepObjAddrs(rhs, IntervalValue(i)));
    as[lhs] = gepAddrs;

    if (const auto *gepObj = SVFUtil::dyn_cast<GepObjVar>(gep->getLHSVar()))
    {
        bufOverflowHelper.addToGepObjOffsetFromBase(gepObj, as.getByteOffset(gep));
    }
}


void AbstractExecution::updateStateOnPhi(const PhiStmt *phi)
{
    const ICFGNode *icfgNode = phi->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(icfgNode);
    u32_t res = phi->getResID();
    auto rhs = AbstractValue();
    // TODO: your code starts from here
    for (u32_t i = 0; i < phi->getOpVarNum(); i++)
    {
        NodeID curId = phi->getOpVarID(i);
        const ICFGNode *opICFGNode = phi->getOpICFGNode(i);
        if (postAbsTrace.find(opICFGNode) != postAbsTrace.end())
        {
            AbstractState tmpEs = postAbsTrace[opICFGNode];
            AbstractState &opAs = getAbsStateFromTrace(opICFGNode);
            const ICFGEdge *edge = icfg->getICFGEdge(opICFGNode, icfgNode, ICFGEdge::IntraCF);
            if (edge)
            {
                const IntraCFGEdge *intraEdge = SVFUtil::cast<IntraCFGEdge>(edge);
                if (intraEdge->getCondition())
                {
                    if (isBranchFeasible(intraEdge, tmpEs))
                        rhs.join_with(opAs[curId]);
                }
                else
                {
                    rhs.join_with(opAs[curId]);
                }
            }
            else
            {
                rhs.join_with(opAs[curId]);
            }
        }
    }
    as[res] = rhs;
}


/// You are required to handle predicates (The program is assumed to have signed ints and also interger-overflow-free),
/// including Add, FAdd, Sub, FSub, Mul, FMul, SDiv, FDiv, UDiv, SRem, FRem, URem
void AbstractExecution::updateStateOnBinary(const BinaryOPStmt *binary)
{
    const ICFGNode *node = binary->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    u32_t op0 = binary->getOpVarID(0);
    u32_t op1 = binary->getOpVarID(1);
    u32_t res = binary->getResID();
    if (!as.inVarToValTable(op0)) as[op0] = IntervalValue::top();
    if (!as.inVarToValTable(op1)) as[op1] = IntervalValue::top();
    IntervalValue &lhs = as[op0].getInterval(), &rhs = as[op1].getInterval();
    IntervalValue resVal;
    auto opCode = binary->getOpcode();

    if (opCode == BinaryOPStmt::Add || opCode == BinaryOPStmt::FAdd)
    {
        // TODO: handle add
        resVal = lhs + rhs;
    }
    else if (opCode == BinaryOPStmt::Sub || opCode == BinaryOPStmt::FSub)
    {
        // TODO: handle subtraction
        resVal = lhs - rhs;
    }
    else if (opCode == BinaryOPStmt::Mul || opCode == BinaryOPStmt::FMul)
    {
        // TODO: handle multiplication
        resVal = lhs * rhs;
    }
    else if (opCode == BinaryOPStmt::SDiv || opCode == BinaryOPStmt::FDiv || opCode == BinaryOPStmt::UDiv)
    {
        // TODO: handle division
        resVal = lhs / rhs;
    }
    else if (opCode == BinaryOPStmt::SRem || opCode == BinaryOPStmt::FRem || opCode == BinaryOPStmt::URem)
    {
        // TODO: handle remainder
        resVal = lhs % rhs;
    }
    else if (opCode == BinaryOPStmt::Xor)
    {
        resVal = lhs ^ rhs;
    }
    else if (opCode == BinaryOPStmt::And)
    {
        resVal = lhs & rhs;
    }
    else if (opCode == BinaryOPStmt::Or)
    {
        resVal = lhs | rhs;
    }
    else if (opCode == BinaryOPStmt::Shl)
    {
        resVal = lhs << rhs;
    }
    else if (opCode == BinaryOPStmt::AShr || opCode == BinaryOPStmt::LShr)
    {
        resVal = lhs >> rhs;
    }
    as[res] = resVal;
}

/// Handle cycle WTO
void AbstractExecution::handleCycleWTO(const ICFGCycleWTO *cycle)
{
    const ICFGNode *cycle_head = cycle->head()->getICFGNode();
    // Flag to indicate if we are in the increasing phase
    bool increasing = true;
    // Infinite loop until a fixpoint is reached,
    for (u32_t cur_iter = 0;; cur_iter++)
    {
        // TODO: your code start from here
        if (!mergeStatesFromPredecessors(cycle_head, preAbsTrace[cycle_head]))
            return;

        if (cur_iter >= Options::WidenDelay())
        {
            AbstractState prev_head_state = postAbsTrace[cycle_head];
            handleSingletonWTO(cycle->head());
            AbstractState cur_head_state = postAbsTrace[cycle_head];
            if (increasing)
            {
                postAbsTrace[cycle_head] = prev_head_state.widening(cur_head_state);
                if (postAbsTrace[cycle_head] == prev_head_state)
                {
                    increasing = false;
                    continue;
                }
            }
            else
            {
                postAbsTrace[cycle_head] = prev_head_state.narrowing(cur_head_state);
                if (postAbsTrace[cycle_head] == prev_head_state)
                {
                    break;
                }
            }
        }
        else
        {
            handleSingletonWTO(cycle->head());
        }
        handleWTOComponents(cycle->getWTOComponents());
    }
}

/// Abstract state updates on an CallPE
void AbstractExecution::updateStateOnCall(const CallPE *call)
{
    const ICFGNode *node = call->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    NodeID lhs = call->getLHSVarID();
    NodeID rhs = call->getRHSVarID();
    as[lhs] = as[rhs];
}

/// Abstract state updates on an RetPE
void AbstractExecution::updateStateOnRet(const RetPE *retPE)
{
    const ICFGNode *node = retPE->getICFGNode();
    AbstractState &as = getAbsStateFromTrace(node);
    NodeID lhs = retPE->getLHSVarID();
    NodeID rhs = retPE->getRHSVarID();
    as[lhs] = as[rhs];
}
