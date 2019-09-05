def pmaddwd1 : instruction :=
  definst "pmaddwd" $ do
    pattern fun (v_2602 : reg (bv 128)) (v_2603 : reg (bv 128)) => do
      v_4678 <- getRegister v_2602;
      v_4681 <- getRegister v_2603;
      setRegister (lhs.of_reg v_2603) (concat (add (mul (sext (extract v_4678 16 32) 32) (sext (extract v_4681 16 32) 32)) (mul (sext (extract v_4678 0 16) 32) (sext (extract v_4681 0 16) 32))) (concat (add (mul (sext (extract v_4678 48 64) 32) (sext (extract v_4681 48 64) 32)) (mul (sext (extract v_4678 32 48) 32) (sext (extract v_4681 32 48) 32))) (concat (add (mul (sext (extract v_4678 80 96) 32) (sext (extract v_4681 80 96) 32)) (mul (sext (extract v_4678 64 80) 32) (sext (extract v_4681 64 80) 32))) (add (mul (sext (extract v_4678 112 128) 32) (sext (extract v_4681 112 128) 32)) (mul (sext (extract v_4678 96 112) 32) (sext (extract v_4681 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_2599 : Mem) (v_2598 : reg (bv 128)) => do
      v_11585 <- evaluateAddress v_2599;
      v_11586 <- load v_11585 16;
      v_11589 <- getRegister v_2598;
      setRegister (lhs.of_reg v_2598) (concat (add (mul (sext (extract v_11586 16 32) 32) (sext (extract v_11589 16 32) 32)) (mul (sext (extract v_11586 0 16) 32) (sext (extract v_11589 0 16) 32))) (concat (add (mul (sext (extract v_11586 48 64) 32) (sext (extract v_11589 48 64) 32)) (mul (sext (extract v_11586 32 48) 32) (sext (extract v_11589 32 48) 32))) (concat (add (mul (sext (extract v_11586 80 96) 32) (sext (extract v_11589 80 96) 32)) (mul (sext (extract v_11586 64 80) 32) (sext (extract v_11589 64 80) 32))) (add (mul (sext (extract v_11586 112 128) 32) (sext (extract v_11589 112 128) 32)) (mul (sext (extract v_11586 96 112) 32) (sext (extract v_11589 96 112) 32))))));
      pure ()
    pat_end
