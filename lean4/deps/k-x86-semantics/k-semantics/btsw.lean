def btsw1 : instruction :=
  definst "btsw" $ do
    pattern fun (v_3289 : imm int) (v_3292 : reg (bv 16)) => do
      v_6197 <- getRegister v_3292;
      v_6200 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3289 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3292) (bv_or v_6197 (extract (shl (expression.bv_nat 16 1) v_6200) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6197 v_6200) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3296 : reg (bv 16)) (v_3297 : reg (bv 16)) => do
      v_6212 <- getRegister v_3297;
      v_6213 <- getRegister v_3296;
      v_6214 <- eval (bv_and v_6213 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3297) (bv_or v_6212 (extract (shl (expression.bv_nat 16 1) v_6214) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6212 v_6214) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3281 : imm int) (v_3284 : Mem) => do
      v_10794 <- evaluateAddress v_3284;
      v_10795 <- eval (handleImmediateWithSignExtend v_3281 8 8);
      v_10799 <- eval (add v_10794 (concat (expression.bv_nat 59 0) (bv_and (extract v_10795 0 5) (expression.bv_nat 5 1))));
      v_10800 <- load v_10799 1;
      v_10803 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10795 5 8) (expression.bv_nat 3 7)));
      store v_10799 (bv_or v_10800 (extract (shl (expression.bv_nat 8 1) v_10803) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10800 v_10803) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3288 : reg (bv 16)) (v_3287 : Mem) => do
      v_10815 <- evaluateAddress v_3287;
      v_10816 <- getRegister v_3288;
      v_10820 <- eval (add v_10815 (concat (expression.bv_nat 3 0) (extract (sext v_10816 64) 0 61)));
      v_10821 <- load v_10820 1;
      v_10823 <- eval (concat (expression.bv_nat 5 0) (extract v_10816 13 16));
      store v_10820 (bv_or v_10821 (extract (shl (expression.bv_nat 8 1) v_10823) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10821 v_10823) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
