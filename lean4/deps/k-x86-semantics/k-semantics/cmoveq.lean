def cmoveq1 : instruction :=
  definst "cmoveq" $ do
    pattern fun (v_2606 : reg (bv 64)) (v_2607 : reg (bv 64)) => do
      v_4292 <- getRegister zf;
      v_4294 <- getRegister v_2606;
      v_4295 <- getRegister v_2607;
      setRegister (lhs.of_reg v_2607) (mux (eq v_4292 (expression.bv_nat 1 1)) v_4294 v_4295);
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 64)) => do
      v_7928 <- getRegister zf;
      v_7930 <- evaluateAddress v_2601;
      v_7931 <- load v_7930 8;
      v_7932 <- getRegister v_2602;
      setRegister (lhs.of_reg v_2602) (mux (eq v_7928 (expression.bv_nat 1 1)) v_7931 v_7932);
      pure ()
    pat_end
