def cmovnel1 : instruction :=
  definst "cmovnel" $ do
    pattern fun (v_2944 : reg (bv 32)) (v_2945 : reg (bv 32)) => do
      v_4658 <- getRegister zf;
      v_4660 <- getRegister v_2944;
      v_4661 <- getRegister v_2945;
      setRegister (lhs.of_reg v_2945) (mux (notBool_ v_4658) v_4660 v_4661);
      pure ()
    pat_end;
    pattern fun (v_2937 : Mem) (v_2940 : reg (bv 32)) => do
      v_8009 <- getRegister zf;
      v_8011 <- evaluateAddress v_2937;
      v_8012 <- load v_8011 4;
      v_8013 <- getRegister v_2940;
      setRegister (lhs.of_reg v_2940) (mux (notBool_ v_8009) v_8012 v_8013);
      pure ()
    pat_end
