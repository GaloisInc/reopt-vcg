def pmovzxwd1 : instruction :=
  definst "pmovzxwd" $ do
    pattern fun (v_2847 : reg (bv 128)) (v_2848 : reg (bv 128)) => do
      v_5623 <- getRegister v_2847;
      setRegister (lhs.of_reg v_2848) (concat (expression.bv_nat 16 0) (concat (extract v_5623 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5623 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5623 96 112) (concat (expression.bv_nat 16 0) (extract v_5623 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2843 : Mem) (v_2844 : reg (bv 128)) => do
      v_12342 <- evaluateAddress v_2843;
      v_12343 <- load v_12342 8;
      setRegister (lhs.of_reg v_2844) (concat (expression.bv_nat 16 0) (concat (extract v_12343 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12343 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12343 32 48) (concat (expression.bv_nat 16 0) (extract v_12343 48 64))))))));
      pure ()
    pat_end
