def vpmovzxwq1 : instruction :=
  definst "vpmovzxwq" $ do
    pattern fun (v_2854 : reg (bv 128)) (v_2855 : reg (bv 128)) => do
      v_5956 <- getRegister v_2854;
      setRegister (lhs.of_reg v_2855) (concat (expression.bv_nat 48 0) (concat (extract v_5956 96 112) (concat (expression.bv_nat 48 0) (extract v_5956 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2864 : reg (bv 128)) (v_2863 : reg (bv 256)) => do
      v_5967 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2863) (concat (expression.bv_nat 48 0) (concat (extract v_5967 64 80) (concat (expression.bv_nat 48 0) (concat (extract v_5967 80 96) (concat (expression.bv_nat 48 0) (concat (extract v_5967 96 112) (concat (expression.bv_nat 48 0) (extract v_5967 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2849 : Mem) (v_2850 : reg (bv 128)) => do
      v_12321 <- evaluateAddress v_2849;
      v_12322 <- load v_12321 4;
      setRegister (lhs.of_reg v_2850) (concat (expression.bv_nat 48 0) (concat (extract v_12322 0 16) (concat (expression.bv_nat 48 0) (extract v_12322 16 32))));
      pure ()
    pat_end;
    pattern fun (v_2858 : Mem) (v_2859 : reg (bv 256)) => do
      v_12329 <- evaluateAddress v_2858;
      v_12330 <- load v_12329 8;
      setRegister (lhs.of_reg v_2859) (concat (expression.bv_nat 48 0) (concat (extract v_12330 0 16) (concat (expression.bv_nat 48 0) (concat (extract v_12330 16 32) (concat (expression.bv_nat 48 0) (concat (extract v_12330 32 48) (concat (expression.bv_nat 48 0) (extract v_12330 48 64))))))));
      pure ()
    pat_end
