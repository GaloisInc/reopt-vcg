def pmullw1 : instruction :=
  definst "pmullw" $ do
    pattern fun (v_2819 : reg (bv 128)) (v_2820 : reg (bv 128)) => do
      v_5980 <- getRegister v_2820;
      v_5984 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2820) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 0 16))) (mi 32 (svalueMInt (extract v_5984 0 16)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 16 32))) (mi 32 (svalueMInt (extract v_5984 16 32)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 32 48))) (mi 32 (svalueMInt (extract v_5984 32 48)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 48 64))) (mi 32 (svalueMInt (extract v_5984 48 64)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 64 80))) (mi 32 (svalueMInt (extract v_5984 64 80)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 80 96))) (mi 32 (svalueMInt (extract v_5984 80 96)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_5980 96 112))) (mi 32 (svalueMInt (extract v_5984 96 112)))) 16 32) (extract (mul (mi 32 (svalueMInt (extract v_5980 112 128))) (mi 32 (svalueMInt (extract v_5984 112 128)))) 16 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2814 : Mem) (v_2815 : reg (bv 128)) => do
      v_13228 <- getRegister v_2815;
      v_13232 <- evaluateAddress v_2814;
      v_13233 <- load v_13232 16;
      setRegister (lhs.of_reg v_2815) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 0 16))) (mi 32 (svalueMInt (extract v_13233 0 16)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 16 32))) (mi 32 (svalueMInt (extract v_13233 16 32)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 32 48))) (mi 32 (svalueMInt (extract v_13233 32 48)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 48 64))) (mi 32 (svalueMInt (extract v_13233 48 64)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 64 80))) (mi 32 (svalueMInt (extract v_13233 64 80)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 80 96))) (mi 32 (svalueMInt (extract v_13233 80 96)))) 16 32) (concat (extract (mul (mi 32 (svalueMInt (extract v_13228 96 112))) (mi 32 (svalueMInt (extract v_13233 96 112)))) 16 32) (extract (mul (mi 32 (svalueMInt (extract v_13228 112 128))) (mi 32 (svalueMInt (extract v_13233 112 128)))) 16 32))))))));
      pure ()
    pat_end
