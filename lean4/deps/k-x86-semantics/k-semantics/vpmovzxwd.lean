def vpmovzxwd1 : instruction :=
  definst "vpmovzxwd" $ do
    pattern fun (v_2771 : reg (bv 128)) (v_2772 : reg (bv 128)) => do
      v_5912 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2772) (concat (expression.bv_nat 16 0) (concat (extract v_5912 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5912 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5912 96 112) (concat (expression.bv_nat 16 0) (extract v_5912 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2780 : reg (bv 128)) (v_2781 : reg (bv 256)) => do
      v_5929 <- getRegister v_2780;
      setRegister (lhs.of_reg v_2781) (concat (expression.bv_nat 16 0) (concat (extract v_5929 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_5929 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_5929 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_5929 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_5929 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5929 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5929 96 112) (concat (expression.bv_nat 16 0) (extract v_5929 112 128))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) (v_2767 : reg (bv 128)) => do
      v_13030 <- evaluateAddress v_2768;
      v_13031 <- load v_13030 8;
      setRegister (lhs.of_reg v_2767) (concat (expression.bv_nat 16 0) (concat (extract v_13031 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_13031 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_13031 32 48) (concat (expression.bv_nat 16 0) (extract v_13031 48 64))))))));
      pure ()
    pat_end;
    pattern fun (v_2776 : Mem) (v_2777 : reg (bv 256)) => do
      v_13044 <- evaluateAddress v_2776;
      v_13045 <- load v_13044 16;
      setRegister (lhs.of_reg v_2777) (concat (expression.bv_nat 16 0) (concat (extract v_13045 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_13045 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_13045 32 48) (concat (expression.bv_nat 16 0) (concat (extract v_13045 48 64) (concat (expression.bv_nat 16 0) (concat (extract v_13045 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_13045 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_13045 96 112) (concat (expression.bv_nat 16 0) (extract v_13045 112 128))))))))))))))));
      pure ()
    pat_end
