def vdivsd1 : instruction :=
  definst "vdivsd" $ do
    pattern fun (v_3391 : reg (bv 128)) (v_3392 : reg (bv 128)) (v_3393 : reg (bv 128)) => do
      v_6581 <- getRegister v_3392;
      v_6585 <- getRegister v_3391;
      setRegister (lhs.of_reg v_3393) (concat (extract v_6581 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6581 64 128) 53 11) (MInt2Float (extract v_6585 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3383 : Mem) (v_3386 : reg (bv 128)) (v_3387 : reg (bv 128)) => do
      v_10737 <- getRegister v_3386;
      v_10741 <- evaluateAddress v_3383;
      v_10742 <- load v_10741 8;
      setRegister (lhs.of_reg v_3387) (concat (extract v_10737 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10737 64 128) 53 11) (MInt2Float v_10742 53 11)) 64));
      pure ()
    pat_end
