def cmovneq1 : instruction :=
  definst "cmovneq" $ do
    pattern fun (v_2872 : reg (bv 64)) (v_2873 : reg (bv 64)) => do
      v_4665 <- getRegister zf;
      v_4668 <- getRegister v_2872;
      v_4669 <- getRegister v_2873;
      setRegister (lhs.of_reg v_2873) (mux (notBool_ (eq v_4665 (expression.bv_nat 1 1))) v_4668 v_4669);
      pure ()
    pat_end;
    pattern fun (v_2868 : Mem) (v_2869 : reg (bv 64)) => do
      v_8225 <- getRegister zf;
      v_8228 <- evaluateAddress v_2868;
      v_8229 <- load v_8228 8;
      v_8230 <- getRegister v_2869;
      setRegister (lhs.of_reg v_2869) (mux (notBool_ (eq v_8225 (expression.bv_nat 1 1))) v_8229 v_8230);
      pure ()
    pat_end
