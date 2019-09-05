def btsw1 : instruction :=
  definst "btsw" $ do
    pattern fun (v_3264 : imm int) (v_3262 : reg (bv 16)) => do
      v_6316 <- getRegister v_3262;
      v_6319 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3264 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3262) (bv_or v_6316 (extract (shl (expression.bv_nat 16 1) v_6319) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6316 v_6319) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3267 : reg (bv 16)) (v_3268 : reg (bv 16)) => do
      v_6331 <- getRegister v_3268;
      v_6332 <- getRegister v_3267;
      v_6333 <- eval (bv_and v_6332 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3268) (bv_or v_6331 (extract (shl (expression.bv_nat 16 1) v_6333) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6331 v_6333) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3255 : imm int) (v_3257 : Mem) => do
      v_11070 <- evaluateAddress v_3257;
      v_11071 <- eval (handleImmediateWithSignExtend v_3255 8 8);
      v_11075 <- eval (add v_11070 (concat (expression.bv_nat 59 0) (bv_and (extract v_11071 0 5) (expression.bv_nat 5 1))));
      v_11076 <- load v_11075 1;
      v_11079 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_11071 5 8) (expression.bv_nat 3 7)));
      store v_11075 (bv_or v_11076 (extract (shl (expression.bv_nat 8 1) v_11079) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_11076 v_11079) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3258 : reg (bv 16)) (v_3261 : Mem) => do
      v_11091 <- evaluateAddress v_3261;
      v_11092 <- getRegister v_3258;
      v_11096 <- eval (add v_11091 (concat (expression.bv_nat 3 0) (extract (sext v_11092 64) 0 61)));
      v_11097 <- load v_11096 1;
      v_11099 <- eval (concat (expression.bv_nat 5 0) (extract v_11092 13 16));
      store v_11096 (bv_or v_11097 (extract (shl (expression.bv_nat 8 1) v_11099) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_11097 v_11099) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
