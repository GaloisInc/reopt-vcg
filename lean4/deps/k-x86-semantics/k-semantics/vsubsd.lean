def vsubsd1 : instruction :=
  definst "vsubsd" $ do
    pattern fun (v_3151 : reg (bv 128)) (v_3152 : reg (bv 128)) (v_3153 : reg (bv 128)) => do
      v_7283 <- getRegister v_3152;
      v_7287 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3153) (concat (extract v_7283 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7283 64 128) 53 11) (MInt2Float (extract v_7287 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3145 : Mem) (v_3146 : reg (bv 128)) (v_3147 : reg (bv 128)) => do
      v_13193 <- getRegister v_3146;
      v_13197 <- evaluateAddress v_3145;
      v_13198 <- load v_13197 8;
      setRegister (lhs.of_reg v_3147) (concat (extract v_13193 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13193 64 128) 53 11) (MInt2Float v_13198 53 11)) 64));
      pure ()
    pat_end
