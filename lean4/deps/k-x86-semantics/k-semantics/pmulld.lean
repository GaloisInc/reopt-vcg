def pmulld1 : instruction :=
  definst "pmulld" $ do
    pattern fun (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_5938 <- getRegister v_2811;
      v_5942 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2811) (concat (extract (mul (mi 64 (svalueMInt (extract v_5938 0 32))) (mi 64 (svalueMInt (extract v_5942 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_5938 32 64))) (mi 64 (svalueMInt (extract v_5942 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_5938 64 96))) (mi 64 (svalueMInt (extract v_5942 64 96)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_5938 96 128))) (mi 64 (svalueMInt (extract v_5942 96 128)))) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) (v_2806 : reg (bv 128)) => do
      v_13189 <- getRegister v_2806;
      v_13193 <- evaluateAddress v_2805;
      v_13194 <- load v_13193 16;
      setRegister (lhs.of_reg v_2806) (concat (extract (mul (mi 64 (svalueMInt (extract v_13189 0 32))) (mi 64 (svalueMInt (extract v_13194 0 32)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13189 32 64))) (mi 64 (svalueMInt (extract v_13194 32 64)))) 32 64) (concat (extract (mul (mi 64 (svalueMInt (extract v_13189 64 96))) (mi 64 (svalueMInt (extract v_13194 64 96)))) 32 64) (extract (mul (mi 64 (svalueMInt (extract v_13189 96 128))) (mi 64 (svalueMInt (extract v_13194 96 128)))) 32 64))));
      pure ()
    pat_end
