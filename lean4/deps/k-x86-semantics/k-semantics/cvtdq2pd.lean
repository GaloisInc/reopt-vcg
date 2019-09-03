def cvtdq2pd1 : instruction :=
  definst "cvtdq2pd" $ do
    pattern fun (v_2476 : reg (bv 128)) (v_2477 : reg (bv 128)) => do
      v_4057 <- getRegister v_2476;
      setRegister (lhs.of_reg v_2477) (concat (Float2MInt (Int2Float (svalueMInt (extract v_4057 64 96)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_4057 96 128)) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2472 : reg (bv 128)) => do
      v_8291 <- evaluateAddress v_2470;
      v_8292 <- load v_8291 8;
      setRegister (lhs.of_reg v_2472) (concat (Float2MInt (Int2Float (svalueMInt (extract v_8292 0 32)) 53 11) 64) (Float2MInt (Int2Float (svalueMInt (extract v_8292 32 64)) 53 11) 64));
      pure ()
    pat_end
