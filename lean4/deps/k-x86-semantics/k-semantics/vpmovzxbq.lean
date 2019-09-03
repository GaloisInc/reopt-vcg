def vpmovzxbq1 : instruction :=
  definst "vpmovzxbq" $ do
    pattern fun (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_5721 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (expression.bv_nat 56 0) (concat (extract v_5721 112 120) (concat (expression.bv_nat 56 0) (extract v_5721 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2738 : reg (bv 128)) (v_2740 : reg (bv 256)) => do
      v_5732 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2740) (concat (expression.bv_nat 56 0) (concat (extract v_5732 96 104) (concat (expression.bv_nat 56 0) (concat (extract v_5732 104 112) (concat (expression.bv_nat 56 0) (concat (extract v_5732 112 120) (concat (expression.bv_nat 56 0) (extract v_5732 120 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2724 : Mem) (v_2725 : reg (bv 128)) => do
      v_12366 <- evaluateAddress v_2724;
      v_12367 <- load v_12366 2;
      setRegister (lhs.of_reg v_2725) (concat (expression.bv_nat 56 0) (concat (extract v_12367 0 8) (concat (expression.bv_nat 56 0) (extract v_12367 8 16))));
      pure ()
    pat_end;
    pattern fun (v_2733 : Mem) (v_2735 : reg (bv 256)) => do
      v_12374 <- evaluateAddress v_2733;
      v_12375 <- load v_12374 4;
      setRegister (lhs.of_reg v_2735) (concat (expression.bv_nat 56 0) (concat (extract v_12375 0 8) (concat (expression.bv_nat 56 0) (concat (extract v_12375 8 16) (concat (expression.bv_nat 56 0) (concat (extract v_12375 16 24) (concat (expression.bv_nat 56 0) (extract v_12375 24 32))))))));
      pure ()
    pat_end
