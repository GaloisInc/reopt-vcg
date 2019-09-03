def cmovbw1 : instruction :=
  definst "cmovbw" $ do
    pattern fun (v_2511 : reg (bv 16)) (v_2512 : reg (bv 16)) => do
      v_4191 <- getRegister cf;
      v_4193 <- getRegister v_2511;
      v_4194 <- getRegister v_2512;
      setRegister (lhs.of_reg v_2512) (mux (eq v_4191 (expression.bv_nat 1 1)) v_4193 v_4194);
      pure ()
    pat_end;
    pattern fun (v_2505 : Mem) (v_2507 : reg (bv 16)) => do
      v_7880 <- getRegister cf;
      v_7882 <- evaluateAddress v_2505;
      v_7883 <- load v_7882 2;
      v_7884 <- getRegister v_2507;
      setRegister (lhs.of_reg v_2507) (mux (eq v_7880 (expression.bv_nat 1 1)) v_7883 v_7884);
      pure ()
    pat_end
