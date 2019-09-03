def divps1 : instruction :=
  definst "divps" $ do
    pattern fun (v_2734 : reg (bv 128)) (v_2735 : reg (bv 128)) => do
      v_4549 <- getRegister v_2735;
      v_4552 <- getRegister v_2734;
      setRegister (lhs.of_reg v_2735) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4549 0 32) 24 8) (MInt2Float (extract v_4552 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4549 32 64) 24 8) (MInt2Float (extract v_4552 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4549 64 96) 24 8) (MInt2Float (extract v_4552 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4549 96 128) 24 8) (MInt2Float (extract v_4552 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2730 : Mem) (v_2731 : reg (bv 128)) => do
      v_8291 <- getRegister v_2731;
      v_8294 <- evaluateAddress v_2730;
      v_8295 <- load v_8294 16;
      setRegister (lhs.of_reg v_2731) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8291 0 32) 24 8) (MInt2Float (extract v_8295 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8291 32 64) 24 8) (MInt2Float (extract v_8295 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8291 64 96) 24 8) (MInt2Float (extract v_8295 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8291 96 128) 24 8) (MInt2Float (extract v_8295 96 128) 24 8)) 32))));
      pure ()
    pat_end
