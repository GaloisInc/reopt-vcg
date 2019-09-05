def btrl1 : instruction :=
  definst "btrl" $ do
    pattern fun (v_3173 : imm int) (v_3175 : reg (bv 32)) => do
      v_6125 <- getRegister v_3175;
      v_6128 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3173 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3175) (bv_and v_6125 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6128) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6125 v_6128) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3179 : reg (bv 32)) (v_3180 : reg (bv 32)) => do
      v_6141 <- getRegister v_3180;
      v_6142 <- getRegister v_3179;
      v_6143 <- eval (bv_and v_6142 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3180) (bv_and v_6141 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6143) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6141 v_6143) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3165 : imm int) (v_3167 : Mem) => do
      v_10861 <- evaluateAddress v_3167;
      v_10862 <- eval (handleImmediateWithSignExtend v_3165 8 8);
      v_10866 <- eval (add v_10861 (concat (expression.bv_nat 59 0) (bv_and (extract v_10862 0 5) (expression.bv_nat 5 3))));
      v_10867 <- load v_10866 1;
      v_10870 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10862 5 8) (expression.bv_nat 3 7)));
      store v_10866 (bv_and v_10867 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10870) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10867 v_10870) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3170 : reg (bv 32)) (v_3171 : Mem) => do
      v_10883 <- evaluateAddress v_3171;
      v_10884 <- getRegister v_3170;
      v_10888 <- eval (add v_10883 (concat (expression.bv_nat 3 0) (extract (sext v_10884 64) 0 61)));
      v_10889 <- load v_10888 1;
      v_10891 <- eval (concat (expression.bv_nat 5 0) (extract v_10884 29 32));
      store v_10888 (bv_and v_10889 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10891) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10889 v_10891) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
