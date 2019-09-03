def cmovzl1 : instruction :=
  definst "cmovzl" $ do
    pattern fun (v_3277 : reg (bv 32)) (v_3278 : reg (bv 32)) => do
      v_5172 <- getRegister zf;
      v_5174 <- getRegister v_3277;
      v_5175 <- getRegister v_3278;
      setRegister (lhs.of_reg v_3278) (mux (eq v_5172 (expression.bv_nat 1 1)) v_5174 v_5175);
      pure ()
    pat_end;
    pattern fun (v_3273 : Mem) (v_3274 : reg (bv 32)) => do
      v_8625 <- getRegister zf;
      v_8627 <- evaluateAddress v_3273;
      v_8628 <- load v_8627 4;
      v_8629 <- getRegister v_3274;
      setRegister (lhs.of_reg v_3274) (mux (eq v_8625 (expression.bv_nat 1 1)) v_8628 v_8629);
      pure ()
    pat_end
