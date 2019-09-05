def subps1 : instruction :=
  definst "subps" $ do
    pattern fun (v_3251 : reg (bv 128)) (v_3252 : reg (bv 128)) => do
      v_6464 <- getRegister v_3252;
      v_6467 <- getRegister v_3251;
      setRegister (lhs.of_reg v_3252) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6464 0 32) 24 8) (MInt2Float (extract v_6467 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6464 32 64) 24 8) (MInt2Float (extract v_6467 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6464 64 96) 24 8) (MInt2Float (extract v_6467 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6464 96 128) 24 8) (MInt2Float (extract v_6467 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3248 : Mem) (v_3247 : reg (bv 128)) => do
      v_9305 <- getRegister v_3247;
      v_9308 <- evaluateAddress v_3248;
      v_9309 <- load v_9308 16;
      setRegister (lhs.of_reg v_3247) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9305 0 32) 24 8) (MInt2Float (extract v_9309 0 32) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9305 32 64) 24 8) (MInt2Float (extract v_9309 32 64) 24 8)) 32) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9305 64 96) 24 8) (MInt2Float (extract v_9309 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9305 96 128) 24 8) (MInt2Float (extract v_9309 96 128) 24 8)) 32))));
      pure ()
    pat_end
