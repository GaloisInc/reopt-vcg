def pmovzxwd1 : instruction :=
  definst "pmovzxwd" $ do
    pattern fun (v_2819 : reg (bv 128)) (v_2820 : reg (bv 128)) => do
      v_5596 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2820) (concat (expression.bv_nat 16 0) (concat (extract v_5596 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5596 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5596 96 112) (concat (expression.bv_nat 16 0) (extract v_5596 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2816 : Mem) (v_2815 : reg (bv 128)) => do
      v_12366 <- evaluateAddress v_2816;
      v_12367 <- load v_12366 8;
      setRegister (lhs.of_reg v_2815) (concat (expression.bv_nat 16 0) (concat (extract v_12367 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12367 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12367 32 48) (concat (expression.bv_nat 16 0) (extract v_12367 48 64))))))));
      pure ()
    pat_end
