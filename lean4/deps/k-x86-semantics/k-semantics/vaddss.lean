def vaddss1 : instruction :=
  definst "vaddss" $ do
    pattern fun (v_2625 : reg (bv 128)) (v_2626 : reg (bv 128)) (v_2627 : reg (bv 128)) => do
      v_4983 <- getRegister v_2626;
      v_4987 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2627) (concat (extract v_4983 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4983 96 128) 24 8) (MInt2Float (extract v_4987 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2617 : Mem) (v_2620 : reg (bv 128)) (v_2621 : reg (bv 128)) => do
      v_9431 <- getRegister v_2620;
      v_9435 <- evaluateAddress v_2617;
      v_9436 <- load v_9435 4;
      setRegister (lhs.of_reg v_2621) (concat (extract v_9431 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9431 96 128) 24 8) (MInt2Float v_9436 24 8)) 32));
      pure ()
    pat_end
