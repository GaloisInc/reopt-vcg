def cmovncl1 : instruction :=
  definst "cmovncl" $ do
    pattern fun (v_2824 : reg (bv 32)) (v_2825 : reg (bv 32)) => do
      v_4608 <- getRegister cf;
      v_4611 <- getRegister v_2824;
      v_4612 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2825) (mux (notBool_ (eq v_4608 (expression.bv_nat 1 1))) v_4611 v_4612);
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 32)) => do
      v_8220 <- getRegister cf;
      v_8223 <- evaluateAddress v_2820;
      v_8224 <- load v_8223 4;
      v_8225 <- getRegister v_2821;
      setRegister (lhs.of_reg v_2821) (mux (notBool_ (eq v_8220 (expression.bv_nat 1 1))) v_8224 v_8225);
      pure ()
    pat_end
