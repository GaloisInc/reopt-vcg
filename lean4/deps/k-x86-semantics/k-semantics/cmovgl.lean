def cmovgl1 : instruction :=
  definst "cmovgl" $ do
    pattern fun (v_2704 : reg (bv 32)) (v_2705 : reg (bv 32)) => do
      v_4364 <- getRegister zf;
      v_4366 <- getRegister sf;
      v_4367 <- getRegister of;
      v_4370 <- getRegister v_2704;
      v_4371 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2705) (mux (bit_and (notBool_ v_4364) (eq v_4366 v_4367)) v_4370 v_4371);
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2700 : reg (bv 32)) => do
      v_7799 <- getRegister zf;
      v_7801 <- getRegister sf;
      v_7802 <- getRegister of;
      v_7805 <- evaluateAddress v_2697;
      v_7806 <- load v_7805 4;
      v_7807 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2700) (mux (bit_and (notBool_ v_7799) (eq v_7801 v_7802)) v_7806 v_7807);
      pure ()
    pat_end
