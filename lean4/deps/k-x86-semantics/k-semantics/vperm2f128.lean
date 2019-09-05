def vperm2f1281 : instruction :=
  definst "vperm2f128" $ do
    pattern fun (v_3000 : imm int) (v_3001 : reg (bv 256)) (v_3002 : reg (bv 256)) (v_3003 : reg (bv 256)) => do
      v_8036 <- eval (handleImmediateWithSignExtend v_3000 8 8);
      v_8038 <- eval (extract v_8036 2 4);
      v_8040 <- getRegister v_3002;
      v_8041 <- eval (extract v_8040 128 256);
      v_8043 <- eval (extract v_8040 0 128);
      v_8045 <- getRegister v_3001;
      v_8046 <- eval (extract v_8045 128 256);
      v_8047 <- eval (extract v_8045 0 128);
      v_8053 <- eval (extract v_8036 6 8);
      setRegister (lhs.of_reg v_3003) (concat (mux (isBitSet v_8036 0) (expression.bv_nat 128 0) (mux (eq v_8038 (expression.bv_nat 2 0)) v_8041 (mux (eq v_8038 (expression.bv_nat 2 1)) v_8043 (mux (eq v_8038 (expression.bv_nat 2 2)) v_8046 v_8047)))) (mux (isBitSet v_8036 4) (expression.bv_nat 128 0) (mux (eq v_8053 (expression.bv_nat 2 0)) v_8041 (mux (eq v_8053 (expression.bv_nat 2 1)) v_8043 (mux (eq v_8053 (expression.bv_nat 2 2)) v_8046 v_8047)))));
      pure ()
    pat_end;
    pattern fun (v_2994 : imm int) (v_2995 : Mem) (v_2996 : reg (bv 256)) (v_2997 : reg (bv 256)) => do
      v_16587 <- eval (handleImmediateWithSignExtend v_2994 8 8);
      v_16589 <- eval (extract v_16587 2 4);
      v_16591 <- getRegister v_2996;
      v_16592 <- eval (extract v_16591 128 256);
      v_16594 <- eval (extract v_16591 0 128);
      v_16596 <- evaluateAddress v_2995;
      v_16597 <- load v_16596 32;
      v_16598 <- eval (extract v_16597 128 256);
      v_16599 <- eval (extract v_16597 0 128);
      v_16605 <- eval (extract v_16587 6 8);
      setRegister (lhs.of_reg v_2997) (concat (mux (isBitSet v_16587 0) (expression.bv_nat 128 0) (mux (eq v_16589 (expression.bv_nat 2 0)) v_16592 (mux (eq v_16589 (expression.bv_nat 2 1)) v_16594 (mux (eq v_16589 (expression.bv_nat 2 2)) v_16598 v_16599)))) (mux (isBitSet v_16587 4) (expression.bv_nat 128 0) (mux (eq v_16605 (expression.bv_nat 2 0)) v_16592 (mux (eq v_16605 (expression.bv_nat 2 1)) v_16594 (mux (eq v_16605 (expression.bv_nat 2 2)) v_16598 v_16599)))));
      pure ()
    pat_end
