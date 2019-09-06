def pmovzxbq1 : instruction :=
  definst "pmovzxbq" $ do
    pattern fun (v_2820 : reg (bv 128)) (v_2821 : reg (bv 128)) => do
      v_5572 <- getRegister v_2820;
      setRegister (lhs.of_reg v_2821) (concat (expression.bv_nat 56 0) (concat (extract v_5572 112 120) (concat (expression.bv_nat 56 0) (extract v_5572 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2816 : Mem) (v_2817 : reg (bv 128)) => do
      v_12300 <- evaluateAddress v_2816;
      v_12301 <- load v_12300 2;
      setRegister (lhs.of_reg v_2817) (concat (expression.bv_nat 56 0) (concat (extract v_12301 0 8) (concat (expression.bv_nat 56 0) (extract v_12301 8 16))));
      pure ()
    pat_end
