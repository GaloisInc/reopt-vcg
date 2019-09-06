def cmovel1 : instruction :=
  definst "cmovel" $ do
    pattern fun (v_2626 : reg (bv 32)) (v_2627 : reg (bv 32)) => do
      v_4289 <- getRegister zf;
      v_4290 <- getRegister v_2626;
      v_4291 <- getRegister v_2627;
      setRegister (lhs.of_reg v_2627) (mux v_4289 v_4290 v_4291);
      pure ()
    pat_end;
    pattern fun (v_2619 : Mem) (v_2622 : reg (bv 32)) => do
      v_7754 <- getRegister zf;
      v_7755 <- evaluateAddress v_2619;
      v_7756 <- load v_7755 4;
      v_7757 <- getRegister v_2622;
      setRegister (lhs.of_reg v_2622) (mux v_7754 v_7756 v_7757);
      pure ()
    pat_end
