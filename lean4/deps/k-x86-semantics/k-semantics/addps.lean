def addps1 : instruction :=
  definst "addps" $ do
    pattern fun (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_4770 <- getRegister v_2607;
      v_4773 <- getRegister v_2606;
      setRegister (lhs.of_reg v_2607) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4770 0 32) 24 8) (MInt2Float (extract v_4773 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4770 32 64) 24 8) (MInt2Float (extract v_4773 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4770 64 96) 24 8) (MInt2Float (extract v_4773 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4770 96 128) 24 8) (MInt2Float (extract v_4773 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2601 : Mem) (v_2602 : reg (bv 128)) => do
      v_9118 <- getRegister v_2602;
      v_9121 <- evaluateAddress v_2601;
      v_9122 <- load v_9121 16;
      setRegister (lhs.of_reg v_2602) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9118 0 32) 24 8) (MInt2Float (extract v_9122 0 32) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9118 32 64) 24 8) (MInt2Float (extract v_9122 32 64) 24 8)) 32) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9118 64 96) 24 8) (MInt2Float (extract v_9122 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9118 96 128) 24 8) (MInt2Float (extract v_9122 96 128) 24 8)) 32))));
      pure ()
    pat_end
