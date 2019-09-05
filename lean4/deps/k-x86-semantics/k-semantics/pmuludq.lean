def pmuludq1 : instruction :=
  definst "pmuludq" $ do
    pattern fun (v_2891 : reg (bv 128)) (v_2892 : reg (bv 128)) => do
      v_5940 <- getRegister v_2892;
      v_5943 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2892) (concat (mul (concat (expression.bv_nat 32 0) (extract v_5940 32 64)) (concat (expression.bv_nat 32 0) (extract v_5943 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_5940 96 128)) (concat (expression.bv_nat 32 0) (extract v_5943 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2888 : Mem) (v_2887 : reg (bv 128)) => do
      v_12686 <- getRegister v_2887;
      v_12689 <- evaluateAddress v_2888;
      v_12690 <- load v_12689 16;
      setRegister (lhs.of_reg v_2887) (concat (mul (concat (expression.bv_nat 32 0) (extract v_12686 32 64)) (concat (expression.bv_nat 32 0) (extract v_12690 32 64))) (mul (concat (expression.bv_nat 32 0) (extract v_12686 96 128)) (concat (expression.bv_nat 32 0) (extract v_12690 96 128))));
      pure ()
    pat_end
