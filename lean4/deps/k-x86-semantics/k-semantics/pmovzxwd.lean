def pmovzxwd1 : instruction :=
  definst "pmovzxwd" $ do
    pattern fun (v_2770 : reg (bv 128)) (v_2771 : reg (bv 128)) => do
      v_5565 <- getRegister v_2770;
      setRegister (lhs.of_reg v_2771) (concat (expression.bv_nat 16 0) (concat (extract v_5565 64 80) (concat (expression.bv_nat 16 0) (concat (extract v_5565 80 96) (concat (expression.bv_nat 16 0) (concat (extract v_5565 96 112) (concat (expression.bv_nat 16 0) (extract v_5565 112 128))))))));
      pure ()
    pat_end;
    pattern fun (v_2766 : Mem) (v_2767 : reg (bv 128)) => do
      v_12508 <- evaluateAddress v_2766;
      v_12509 <- load v_12508 8;
      setRegister (lhs.of_reg v_2767) (concat (expression.bv_nat 16 0) (concat (extract v_12509 0 16) (concat (expression.bv_nat 16 0) (concat (extract v_12509 16 32) (concat (expression.bv_nat 16 0) (concat (extract v_12509 32 48) (concat (expression.bv_nat 16 0) (extract v_12509 48 64))))))));
      pure ()
    pat_end
