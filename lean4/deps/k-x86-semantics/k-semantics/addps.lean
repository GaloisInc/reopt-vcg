def addps1 : instruction :=
  definst "addps" $ do
    pattern fun (v_2670 : reg (bv 128)) (v_2671 : reg (bv 128)) => do
      v_4761 <- getRegister v_2671;
      v_4764 <- getRegister v_2670;
      setRegister (lhs.of_reg v_2671) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4761 0 32) 24 8) (MInt2Float (extract v_4764 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4761 32 64) 24 8) (MInt2Float (extract v_4764 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4761 64 96) 24 8) (MInt2Float (extract v_4764 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4761 96 128) 24 8) (MInt2Float (extract v_4764 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2665 : Mem) (v_2666 : reg (bv 128)) => do
      v_8933 <- getRegister v_2666;
      v_8936 <- evaluateAddress v_2665;
      v_8937 <- load v_8936 16;
      setRegister (lhs.of_reg v_2666) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8933 0 32) 24 8) (MInt2Float (extract v_8937 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8933 32 64) 24 8) (MInt2Float (extract v_8937 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8933 64 96) 24 8) (MInt2Float (extract v_8937 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8933 96 128) 24 8) (MInt2Float (extract v_8937 96 128) 24 8)) 32))));
      pure ()
    pat_end
