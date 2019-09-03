def punpckhbw1 : instruction :=
  definst "punpckhbw" $ do
    pattern fun (v_3176 : reg (bv 128)) (v_3177 : reg (bv 128)) => do
      v_8725 <- getRegister v_3176;
      v_8727 <- getRegister v_3177;
      setRegister (lhs.of_reg v_3177) (concat (concat (extract v_8725 0 8) (extract v_8727 0 8)) (concat (concat (extract v_8725 8 16) (extract v_8727 8 16)) (concat (concat (extract v_8725 16 24) (extract v_8727 16 24)) (concat (concat (extract v_8725 24 32) (extract v_8727 24 32)) (concat (concat (extract v_8725 32 40) (extract v_8727 32 40)) (concat (concat (extract v_8725 40 48) (extract v_8727 40 48)) (concat (concat (extract v_8725 48 56) (extract v_8727 48 56)) (concat (extract v_8725 56 64) (extract v_8727 56 64)))))))));
      pure ()
    pat_end;
    pattern fun (v_3172 : Mem) (v_3173 : reg (bv 128)) => do
      v_15316 <- evaluateAddress v_3172;
      v_15317 <- load v_15316 16;
      v_15319 <- getRegister v_3173;
      setRegister (lhs.of_reg v_3173) (concat (concat (extract v_15317 0 8) (extract v_15319 0 8)) (concat (concat (extract v_15317 8 16) (extract v_15319 8 16)) (concat (concat (extract v_15317 16 24) (extract v_15319 16 24)) (concat (concat (extract v_15317 24 32) (extract v_15319 24 32)) (concat (concat (extract v_15317 32 40) (extract v_15319 32 40)) (concat (concat (extract v_15317 40 48) (extract v_15319 40 48)) (concat (concat (extract v_15317 48 56) (extract v_15319 48 56)) (concat (extract v_15317 56 64) (extract v_15319 56 64)))))))));
      pure ()
    pat_end
