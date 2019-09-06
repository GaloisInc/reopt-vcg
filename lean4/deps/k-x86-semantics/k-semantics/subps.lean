def subps1 : instruction :=
  definst "subps" $ do
    pattern fun (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) => do
      v_5909 <- getRegister v_3280;
      v_5912 <- getRegister v_3279;
      setRegister (lhs.of_reg v_3280) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5909 0 32) 24 8) (MInt2Float (extract v_5912 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5909 32 64) 24 8) (MInt2Float (extract v_5912 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5909 64 96) 24 8) (MInt2Float (extract v_5912 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5909 96 128) 24 8) (MInt2Float (extract v_5912 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3275 : Mem) (v_3276 : reg (bv 128)) => do
      v_8695 <- getRegister v_3276;
      v_8698 <- evaluateAddress v_3275;
      v_8699 <- load v_8698 16;
      setRegister (lhs.of_reg v_3276) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8695 0 32) 24 8) (MInt2Float (extract v_8699 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8695 32 64) 24 8) (MInt2Float (extract v_8699 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8695 64 96) 24 8) (MInt2Float (extract v_8699 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8695 96 128) 24 8) (MInt2Float (extract v_8699 96 128) 24 8)) 32))));
      pure ()
    pat_end
