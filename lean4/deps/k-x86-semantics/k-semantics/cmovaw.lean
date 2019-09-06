def cmovaw1 : instruction :=
  definst "cmovaw" $ do
    pattern fun (v_2509 : reg (bv 16)) (v_2510 : reg (bv 16)) => do
      v_4174 <- getRegister cf;
      v_4176 <- getRegister zf;
      v_4179 <- getRegister v_2509;
      v_4180 <- getRegister v_2510;
      setRegister (lhs.of_reg v_2510) (mux (bit_and (notBool_ v_4174) (notBool_ v_4176)) v_4179 v_4180);
      pure ()
    pat_end;
    pattern fun (v_2505 : Mem) (v_2506 : reg (bv 16)) => do
      v_7681 <- getRegister cf;
      v_7683 <- getRegister zf;
      v_7686 <- evaluateAddress v_2505;
      v_7687 <- load v_7686 2;
      v_7688 <- getRegister v_2506;
      setRegister (lhs.of_reg v_2506) (mux (bit_and (notBool_ v_7681) (notBool_ v_7683)) v_7687 v_7688);
      pure ()
    pat_end
