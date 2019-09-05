def pmovzxbq1 : instruction :=
  definst "pmovzxbq" $ do
    pattern fun (v_2792 : reg (bv 128)) (v_2793 : reg (bv 128)) => do
      v_5545 <- getRegister v_2792;
      setRegister (lhs.of_reg v_2793) (concat (expression.bv_nat 56 0) (concat (extract v_5545 112 120) (concat (expression.bv_nat 56 0) (extract v_5545 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2789 : Mem) (v_2788 : reg (bv 128)) => do
      v_12324 <- evaluateAddress v_2789;
      v_12325 <- load v_12324 2;
      setRegister (lhs.of_reg v_2788) (concat (expression.bv_nat 56 0) (concat (extract v_12325 0 8) (concat (expression.bv_nat 56 0) (extract v_12325 8 16))));
      pure ()
    pat_end
