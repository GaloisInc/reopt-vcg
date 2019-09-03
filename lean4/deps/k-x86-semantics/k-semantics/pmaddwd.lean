def pmaddwd1 : instruction :=
  definst "pmaddwd" $ do
    pattern fun (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_4698 <- getRegister v_2539;
      v_4702 <- getRegister v_2540;
      setRegister (lhs.of_reg v_2540) (concat (add (mul (mi 32 (svalueMInt (extract v_4698 16 32))) (mi 32 (svalueMInt (extract v_4702 16 32)))) (mul (mi 32 (svalueMInt (extract v_4698 0 16))) (mi 32 (svalueMInt (extract v_4702 0 16))))) (concat (add (mul (mi 32 (svalueMInt (extract v_4698 48 64))) (mi 32 (svalueMInt (extract v_4702 48 64)))) (mul (mi 32 (svalueMInt (extract v_4698 32 48))) (mi 32 (svalueMInt (extract v_4702 32 48))))) (concat (add (mul (mi 32 (svalueMInt (extract v_4698 80 96))) (mi 32 (svalueMInt (extract v_4702 80 96)))) (mul (mi 32 (svalueMInt (extract v_4698 64 80))) (mi 32 (svalueMInt (extract v_4702 64 80))))) (add (mul (mi 32 (svalueMInt (extract v_4698 112 128))) (mi 32 (svalueMInt (extract v_4702 112 128)))) (mul (mi 32 (svalueMInt (extract v_4698 96 112))) (mi 32 (svalueMInt (extract v_4702 96 112))))))));
      pure ()
    pat_end;
    pattern fun (v_2534 : Mem) (v_2535 : reg (bv 128)) => do
      v_12104 <- evaluateAddress v_2534;
      v_12105 <- load v_12104 16;
      v_12109 <- getRegister v_2535;
      setRegister (lhs.of_reg v_2535) (concat (add (mul (mi 32 (svalueMInt (extract v_12105 16 32))) (mi 32 (svalueMInt (extract v_12109 16 32)))) (mul (mi 32 (svalueMInt (extract v_12105 0 16))) (mi 32 (svalueMInt (extract v_12109 0 16))))) (concat (add (mul (mi 32 (svalueMInt (extract v_12105 48 64))) (mi 32 (svalueMInt (extract v_12109 48 64)))) (mul (mi 32 (svalueMInt (extract v_12105 32 48))) (mi 32 (svalueMInt (extract v_12109 32 48))))) (concat (add (mul (mi 32 (svalueMInt (extract v_12105 80 96))) (mi 32 (svalueMInt (extract v_12109 80 96)))) (mul (mi 32 (svalueMInt (extract v_12105 64 80))) (mi 32 (svalueMInt (extract v_12109 64 80))))) (add (mul (mi 32 (svalueMInt (extract v_12105 112 128))) (mi 32 (svalueMInt (extract v_12109 112 128)))) (mul (mi 32 (svalueMInt (extract v_12105 96 112))) (mi 32 (svalueMInt (extract v_12109 96 112))))))));
      pure ()
    pat_end
