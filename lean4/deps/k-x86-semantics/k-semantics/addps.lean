def addps1 : instruction :=
  definst "addps" $ do
    pattern fun (v_2694 : reg (bv 128)) (v_2695 : reg (bv 128)) => do
      v_4667 <- getRegister v_2695;
      v_4670 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2695) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4667 0 32) 24 8) (MInt2Float (extract v_4670 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4667 32 64) 24 8) (MInt2Float (extract v_4670 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4667 64 96) 24 8) (MInt2Float (extract v_4670 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4667 96 128) 24 8) (MInt2Float (extract v_4670 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2693 : Mem) (v_2690 : reg (bv 128)) => do
      v_8767 <- getRegister v_2690;
      v_8770 <- evaluateAddress v_2693;
      v_8771 <- load v_8770 16;
      setRegister (lhs.of_reg v_2690) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8767 0 32) 24 8) (MInt2Float (extract v_8771 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8767 32 64) 24 8) (MInt2Float (extract v_8771 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8767 64 96) 24 8) (MInt2Float (extract v_8771 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8767 96 128) 24 8) (MInt2Float (extract v_8771 96 128) 24 8)) 32))));
      pure ()
    pat_end
