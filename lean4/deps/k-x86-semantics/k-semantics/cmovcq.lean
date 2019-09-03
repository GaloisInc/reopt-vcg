def cmovcq1 : instruction :=
  definst "cmovcq" $ do
    pattern fun (v_2516 : reg (bv 64)) (v_2517 : reg (bv 64)) => do
      v_4198 <- getRegister cf;
      v_4200 <- getRegister v_2516;
      v_4201 <- getRegister v_2517;
      setRegister (lhs.of_reg v_2517) (mux (eq v_4198 (expression.bv_nat 1 1)) v_4200 v_4201);
      pure ()
    pat_end;
    pattern fun (v_2511 : Mem) (v_2512 : reg (bv 64)) => do
      v_7921 <- getRegister cf;
      v_7923 <- evaluateAddress v_2511;
      v_7924 <- load v_7923 8;
      v_7925 <- getRegister v_2512;
      setRegister (lhs.of_reg v_2512) (mux (eq v_7921 (expression.bv_nat 1 1)) v_7924 v_7925);
      pure ()
    pat_end
