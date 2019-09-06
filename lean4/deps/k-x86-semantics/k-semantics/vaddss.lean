def vaddss1 : instruction :=
  definst "vaddss" $ do
    pattern fun (v_2716 : reg (bv 128)) (v_2717 : reg (bv 128)) (v_2718 : reg (bv 128)) => do
      v_4982 <- getRegister v_2717;
      v_4986 <- getRegister v_2716;
      setRegister (lhs.of_reg v_2718) (concat (extract v_4982 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4982 96 128) 24 8) (MInt2Float (extract v_4986 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2708 : Mem) (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_9270 <- getRegister v_2711;
      v_9274 <- evaluateAddress v_2708;
      v_9275 <- load v_9274 4;
      setRegister (lhs.of_reg v_2712) (concat (extract v_9270 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9270 96 128) 24 8) (MInt2Float v_9275 24 8)) 32));
      pure ()
    pat_end
