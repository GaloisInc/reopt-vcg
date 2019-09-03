def pmovzxbq1 : instruction :=
  definst "pmovzxbq" $ do
    pattern fun (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_5603 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (expression.bv_nat 56 0) (concat (extract v_5603 112 120) (concat (expression.bv_nat 56 0) (extract v_5603 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2724 : Mem) (v_2725 : reg (bv 128)) => do
      v_12881 <- evaluateAddress v_2724;
      v_12882 <- load v_12881 2;
      setRegister (lhs.of_reg v_2725) (concat (expression.bv_nat 56 0) (concat (extract v_12882 0 8) (concat (expression.bv_nat 56 0) (extract v_12882 8 16))));
      pure ()
    pat_end
