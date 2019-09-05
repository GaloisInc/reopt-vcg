def divps1 : instruction :=
  definst "divps" $ do
    pattern fun (v_2799 : reg (bv 128)) (v_2800 : reg (bv 128)) => do
      v_4542 <- getRegister v_2800;
      v_4545 <- getRegister v_2799;
      setRegister (lhs.of_reg v_2800) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4542 0 32) 24 8) (MInt2Float (extract v_4545 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4542 32 64) 24 8) (MInt2Float (extract v_4545 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4542 64 96) 24 8) (MInt2Float (extract v_4545 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4542 96 128) 24 8) (MInt2Float (extract v_4545 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2794 : Mem) (v_2795 : reg (bv 128)) => do
      v_8069 <- getRegister v_2795;
      v_8072 <- evaluateAddress v_2794;
      v_8073 <- load v_8072 16;
      setRegister (lhs.of_reg v_2795) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8069 0 32) 24 8) (MInt2Float (extract v_8073 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8069 32 64) 24 8) (MInt2Float (extract v_8073 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8069 64 96) 24 8) (MInt2Float (extract v_8073 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8069 96 128) 24 8) (MInt2Float (extract v_8073 96 128) 24 8)) 32))));
      pure ()
    pat_end
