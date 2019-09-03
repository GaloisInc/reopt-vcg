def cmovns1 : instruction :=
  definst "cmovns" $ do
    pattern fun (v_3037 : Mem) (v_3036 : reg (bv 32)) => do
      v_9123 <- getRegister sf;
      v_9126 <- evaluateAddress v_3037;
      v_9127 <- load v_9126 4;
      v_9128 <- getRegister v_3036;
      setRegister (lhs.of_reg v_3036) (mux (notBool_ (eq v_9123 (expression.bv_nat 1 1))) v_9127 v_9128);
      pure ()
    pat_end;
    pattern fun (v_3053 : Mem) (v_3054 : reg (bv 64)) => do
      v_9131 <- getRegister sf;
      v_9134 <- evaluateAddress v_3053;
      v_9135 <- load v_9134 8;
      v_9136 <- getRegister v_3054;
      setRegister (lhs.of_reg v_3054) (mux (notBool_ (eq v_9131 (expression.bv_nat 1 1))) v_9135 v_9136);
      pure ()
    pat_end;
    pattern fun (v_3071 : Mem) (v_3070 : reg (bv 16)) => do
      v_9139 <- getRegister sf;
      v_9142 <- evaluateAddress v_3071;
      v_9143 <- load v_9142 2;
      v_9144 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3070) (mux (notBool_ (eq v_9139 (expression.bv_nat 1 1))) v_9143 v_9144);
      pure ()
    pat_end
