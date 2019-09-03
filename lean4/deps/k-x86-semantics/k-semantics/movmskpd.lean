def movmskpd1 : instruction :=
  definst "movmskpd" $ do
    pattern fun (v_2526 : reg (bv 128)) (v_2527 : reg (bv 32)) => do
      v_3943 <- getRegister v_2526;
      setRegister (lhs.of_reg v_2527) (concat (expression.bv_nat 30 0) (concat (extract v_3943 0 1) (extract v_3943 64 65)));
      pure ()
    pat_end;
    pattern fun (v_2531 : reg (bv 128)) (v_2532 : reg (bv 64)) => do
      v_3949 <- getRegister v_2531;
      setRegister (lhs.of_reg v_2532) (concat (expression.bv_nat 62 0) (concat (extract v_3949 0 1) (extract v_3949 64 65)));
      pure ()
    pat_end
