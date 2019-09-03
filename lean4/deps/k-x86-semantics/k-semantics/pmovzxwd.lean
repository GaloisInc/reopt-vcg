def pmovzxwd1 : instruction :=
  definst "pmovzxwd" $ do
    pattern fun (v_2756 : reg (bv 128)) (v_2757 : reg (bv 128)) => do
      v_5654 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2757) (concat (expression.bv_nat 16 0) (concat (extract v_5654 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5654 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5654 96 112) (concat (expression.bv_nat 16 0) (extract v_5654 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2751 : Mem) (v_2752 : reg (bv 128)) => do
      v_12923 <- evaluateAddress v_2751;
      v_12924 <- load v_12923 8;
      setRegister (lhs.of_reg v_2752) (concat (expression.bv_nat 16 0) (concat (extract v_12924 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12924 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12924 32 48) (concat (expression.bv_nat 16 0) (extract v_12924 48 64))))))));
      pure ()
    pat_end
