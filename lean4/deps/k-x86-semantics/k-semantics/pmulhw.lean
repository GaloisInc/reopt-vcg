def pmulhw1 : instruction :=
  definst "pmulhw" $ do
    pattern fun (v_2801 : reg (bv 128)) (v_2802 : reg (bv 128)) => do
      v_5860 <- getRegister v_2802;
      v_5864 <- getRegister v_2801;
      setRegister (lhs.of_reg v_2802) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 0 16))) (mi 32 (svalueMInt (extract v_5864 0 16)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 16 32))) (mi 32 (svalueMInt (extract v_5864 16 32)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 32 48))) (mi 32 (svalueMInt (extract v_5864 32 48)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 48 64))) (mi 32 (svalueMInt (extract v_5864 48 64)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 64 80))) (mi 32 (svalueMInt (extract v_5864 64 80)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 80 96))) (mi 32 (svalueMInt (extract v_5864 80 96)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_5860 96 112))) (mi 32 (svalueMInt (extract v_5864 96 112)))) 0 16) (extract (mul (mi 32 (svalueMInt (extract v_5860 112 128))) (mi 32 (svalueMInt (extract v_5864 112 128)))) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2796 : Mem) (v_2797 : reg (bv 128)) => do
      v_13114 <- getRegister v_2797;
      v_13118 <- evaluateAddress v_2796;
      v_13119 <- load v_13118 16;
      setRegister (lhs.of_reg v_2797) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 0 16))) (mi 32 (svalueMInt (extract v_13119 0 16)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 16 32))) (mi 32 (svalueMInt (extract v_13119 16 32)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 32 48))) (mi 32 (svalueMInt (extract v_13119 32 48)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 48 64))) (mi 32 (svalueMInt (extract v_13119 48 64)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 64 80))) (mi 32 (svalueMInt (extract v_13119 64 80)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 80 96))) (mi 32 (svalueMInt (extract v_13119 80 96)))) 0 16) (concat (extract (mul (mi 32 (svalueMInt (extract v_13114 96 112))) (mi 32 (svalueMInt (extract v_13119 96 112)))) 0 16) (extract (mul (mi 32 (svalueMInt (extract v_13114 112 128))) (mi 32 (svalueMInt (extract v_13119 112 128)))) 0 16))))))));
      pure ()
    pat_end
