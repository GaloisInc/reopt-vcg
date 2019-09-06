def cmovnaq1 : instruction :=
  definst "cmovnaq" $ do
    pattern fun (v_2842 : reg (bv 64)) (v_2843 : reg (bv 64)) => do
      v_4537 <- getRegister cf;
      v_4538 <- getRegister zf;
      v_4540 <- getRegister v_2842;
      v_4541 <- getRegister v_2843;
      setRegister (lhs.of_reg v_2843) (mux (bit_or v_4537 v_4538) v_4540 v_4541);
      pure ()
    pat_end;
    pattern fun (v_2838 : Mem) (v_2839 : reg (bv 64)) => do
      v_7921 <- getRegister cf;
      v_7922 <- getRegister zf;
      v_7924 <- evaluateAddress v_2838;
      v_7925 <- load v_7924 8;
      v_7926 <- getRegister v_2839;
      setRegister (lhs.of_reg v_2839) (mux (bit_or v_7921 v_7922) v_7925 v_7926);
      pure ()
    pat_end
