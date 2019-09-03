def cmovnoq1 : instruction :=
  definst "cmovnoq" $ do
    pattern fun (v_2996 : reg (bv 64)) (v_2997 : reg (bv 64)) => do
      v_4868 <- getRegister of;
      v_4871 <- getRegister v_2996;
      v_4872 <- getRegister v_2997;
      setRegister (lhs.of_reg v_2997) (mux (notBool_ (eq v_4868 (expression.bv_nat 1 1))) v_4871 v_4872);
      pure ()
    pat_end;
    pattern fun (v_2991 : Mem) (v_2992 : reg (bv 64)) => do
      v_8423 <- getRegister of;
      v_8426 <- evaluateAddress v_2991;
      v_8427 <- load v_8426 8;
      v_8428 <- getRegister v_2992;
      setRegister (lhs.of_reg v_2992) (mux (notBool_ (eq v_8423 (expression.bv_nat 1 1))) v_8427 v_8428);
      pure ()
    pat_end
