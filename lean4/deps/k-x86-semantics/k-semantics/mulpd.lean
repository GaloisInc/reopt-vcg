def mulpd1 : instruction :=
  definst "mulpd" $ do
    pattern fun (v_2728 : reg (bv 128)) (v_2729 : reg (bv 128)) => do
      v_4164 <- getRegister v_2729;
      v_4167 <- getRegister v_2728;
      setRegister (lhs.of_reg v_2729) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4164 0 64) 53 11) (MInt2Float (extract v_4167 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4164 64 128) 53 11) (MInt2Float (extract v_4167 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2723 : Mem) (v_2724 : reg (bv 128)) => do
      v_8955 <- getRegister v_2724;
      v_8958 <- evaluateAddress v_2723;
      v_8959 <- load v_8958 16;
      setRegister (lhs.of_reg v_2724) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8955 0 64) 53 11) (MInt2Float (extract v_8959 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8955 64 128) 53 11) (MInt2Float (extract v_8959 64 128) 53 11)) 64));
      pure ()
    pat_end
