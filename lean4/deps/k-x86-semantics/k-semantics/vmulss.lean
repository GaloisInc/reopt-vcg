def vmulss1 : instruction :=
  definst "vmulss" $ do
    pattern fun (v_3213 : reg (bv 128)) (v_3214 : reg (bv 128)) (v_3215 : reg (bv 128)) => do
      v_5351 <- getRegister v_3214;
      v_5355 <- getRegister v_3213;
      setRegister (lhs.of_reg v_3215) (concat (extract v_5351 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5351 96 128) 24 8) (MInt2Float (extract v_5355 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3208 : Mem) (v_3209 : reg (bv 128)) (v_3210 : reg (bv 128)) => do
      v_10462 <- getRegister v_3209;
      v_10466 <- evaluateAddress v_3208;
      v_10467 <- load v_10466 4;
      setRegister (lhs.of_reg v_3210) (concat (extract v_10462 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10462 96 128) 24 8) (MInt2Float v_10467 24 8)) 32));
      pure ()
    pat_end
