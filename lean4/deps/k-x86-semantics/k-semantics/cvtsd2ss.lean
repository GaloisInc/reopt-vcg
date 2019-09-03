def cvtsd2ss1 : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (v_2543 : reg (bv 128)) (v_2544 : reg (bv 128)) => do
      v_4195 <- getRegister v_2544;
      v_4197 <- getRegister v_2543;
      setRegister (lhs.of_reg v_2544) (concat (extract v_4195 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_4197 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2539 : Mem) (v_2540 : reg (bv 128)) => do
      v_8136 <- getRegister v_2540;
      v_8138 <- evaluateAddress v_2539;
      v_8139 <- load v_8138 8;
      setRegister (lhs.of_reg v_2540) (concat (extract v_8136 0 96) (Float2MInt (roundFloat (MInt2Float v_8139 53 11) 24 8) 32));
      pure ()
    pat_end
