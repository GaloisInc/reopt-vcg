def vpmovzxwq1 : instruction :=
  definst "vpmovzxwq" $ do
    pattern fun (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) => do
      v_5983 <- getRegister v_2881;
      setRegister (lhs.of_reg v_2882) (concat (expression.bv_nat 48 0) (concat (extract v_5983 96 112) (concat (expression.bv_nat 48 0) (extract v_5983 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2891 : reg (bv 128)) (v_2890 : reg (bv 256)) => do
      v_5994 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2890) (concat (expression.bv_nat 48 0) (concat (extract v_5994 64 80) (concat (expression.bv_nat 48 0) (concat (extract v_5994 80 96) (concat (expression.bv_nat 48 0) (concat (extract v_5994 96 112) (concat (expression.bv_nat 48 0) (extract v_5994 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2876 : Mem) (v_2877 : reg (bv 128)) => do
      v_12348 <- evaluateAddress v_2876;
      v_12349 <- load v_12348 4;
      setRegister (lhs.of_reg v_2877) (concat (expression.bv_nat 48 0) (concat (extract v_12349 0 16) (concat (expression.bv_nat 48 0) (extract v_12349 16 32))));
      pure ()
    pat_end;
    pattern fun (v_2885 : Mem) (v_2886 : reg (bv 256)) => do
      v_12356 <- evaluateAddress v_2885;
      v_12357 <- load v_12356 8;
      setRegister (lhs.of_reg v_2886) (concat (expression.bv_nat 48 0) (concat (extract v_12357 0 16) (concat (expression.bv_nat 48 0) (concat (extract v_12357 16 32) (concat (expression.bv_nat 48 0) (concat (extract v_12357 32 48) (concat (expression.bv_nat 48 0) (extract v_12357 48 64))))))));
      pure ()
    pat_end
