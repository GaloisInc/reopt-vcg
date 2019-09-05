def vmulss1 : instruction :=
  definst "vmulss" $ do
    pattern fun (v_3188 : reg (bv 128)) (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) => do
      v_5324 <- getRegister v_3189;
      v_5328 <- getRegister v_3188;
      setRegister (lhs.of_reg v_3190) (concat (extract v_5324 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5324 96 128) 24 8) (MInt2Float (extract v_5328 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3183 : Mem) (v_3184 : reg (bv 128)) (v_3185 : reg (bv 128)) => do
      v_10435 <- getRegister v_3184;
      v_10439 <- evaluateAddress v_3183;
      v_10440 <- load v_10439 4;
      setRegister (lhs.of_reg v_3185) (concat (extract v_10435 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10435 96 128) 24 8) (MInt2Float v_10440 24 8)) 32));
      pure ()
    pat_end
