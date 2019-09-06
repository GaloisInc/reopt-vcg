def btsl1 : instruction :=
  definst "btsl" $ do
    pattern fun (v_3253 : imm int) (v_3257 : reg (bv 32)) => do
      v_6123 <- getRegister v_3257;
      v_6126 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3253 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3257) (bv_or v_6123 (extract (shl (expression.bv_nat 32 1) v_6126) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6123 v_6126) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3261 : reg (bv 32)) (v_3262 : reg (bv 32)) => do
      v_6138 <- getRegister v_3262;
      v_6139 <- getRegister v_3261;
      v_6140 <- eval (bv_and v_6139 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3262) (bv_or v_6138 (extract (shl (expression.bv_nat 32 1) v_6140) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6138 v_6140) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3245 : imm int) (v_3248 : Mem) => do
      v_10713 <- evaluateAddress v_3248;
      v_10714 <- eval (handleImmediateWithSignExtend v_3245 8 8);
      v_10718 <- eval (add v_10713 (concat (expression.bv_nat 59 0) (bv_and (extract v_10714 0 5) (expression.bv_nat 5 3))));
      v_10719 <- load v_10718 1;
      v_10722 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10714 5 8) (expression.bv_nat 3 7)));
      store v_10718 (bv_or v_10719 (extract (shl (expression.bv_nat 8 1) v_10722) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10719 v_10722) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3252 : reg (bv 32)) (v_3251 : Mem) => do
      v_10734 <- evaluateAddress v_3251;
      v_10735 <- getRegister v_3252;
      v_10739 <- eval (add v_10734 (concat (expression.bv_nat 3 0) (extract (sext v_10735 64) 0 61)));
      v_10740 <- load v_10739 1;
      v_10742 <- eval (concat (expression.bv_nat 5 0) (extract v_10735 29 32));
      store v_10739 (bv_or v_10740 (extract (shl (expression.bv_nat 8 1) v_10742) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10740 v_10742) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
