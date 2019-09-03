def mulsd1 : instruction :=
  definst "mulsd" $ do
    pattern fun (v_2753 : reg (bv 128)) (v_2754 : reg (bv 128)) => do
      v_4239 <- getRegister v_2754;
      v_4243 <- getRegister v_2753;
      setRegister (lhs.of_reg v_2754) (concat (extract v_4239 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4239 64 128) 53 11) (MInt2Float (extract v_4243 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2749 : reg (bv 128)) => do
      v_9022 <- getRegister v_2749;
      v_9026 <- evaluateAddress v_2748;
      v_9027 <- load v_9026 8;
      setRegister (lhs.of_reg v_2749) (concat (extract v_9022 0 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_9022 64 128) 53 11) (MInt2Float v_9027 53 11)) 64));
      pure ()
    pat_end
