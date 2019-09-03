def subps1 : instruction :=
  definst "subps" $ do
    pattern fun (v_3188 : reg (bv 128)) (v_3189 : reg (bv 128)) => do
      v_7251 <- getRegister v_3189;
      v_7254 <- getRegister v_3188;
      setRegister (lhs.of_reg v_3189) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7251 0 32) 24 8) (MInt2Float (extract v_7254 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7251 32 64) 24 8) (MInt2Float (extract v_7254 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7251 64 96) 24 8) (MInt2Float (extract v_7254 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7251 96 128) 24 8) (MInt2Float (extract v_7254 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3183 : Mem) (v_3184 : reg (bv 128)) => do
      v_10434 <- getRegister v_3184;
      v_10437 <- evaluateAddress v_3183;
      v_10438 <- load v_10437 16;
      setRegister (lhs.of_reg v_3184) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10434 0 32) 24 8) (MInt2Float (extract v_10438 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10434 32 64) 24 8) (MInt2Float (extract v_10438 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10434 64 96) 24 8) (MInt2Float (extract v_10438 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10434 96 128) 24 8) (MInt2Float (extract v_10438 96 128) 24 8)) 32))));
      pure ()
    pat_end
