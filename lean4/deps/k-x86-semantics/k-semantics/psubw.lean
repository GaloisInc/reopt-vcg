def psubw1 : instruction :=
  definst "psubw" $ do
    pattern fun (v_3235 : reg (bv 128)) (v_3236 : reg (bv 128)) => do
      v_8631 <- getRegister v_3236;
      v_8633 <- getRegister v_3235;
      setRegister (lhs.of_reg v_3236) (concat (sub (extract v_8631 0 16) (extract v_8633 0 16)) (concat (sub (extract v_8631 16 32) (extract v_8633 16 32)) (concat (sub (extract v_8631 32 48) (extract v_8633 32 48)) (concat (sub (extract v_8631 48 64) (extract v_8633 48 64)) (concat (sub (extract v_8631 64 80) (extract v_8633 64 80)) (concat (sub (extract v_8631 80 96) (extract v_8633 80 96)) (concat (sub (extract v_8631 96 112) (extract v_8633 96 112)) (sub (extract v_8631 112 128) (extract v_8633 112 128)))))))));
      pure ()
    pat_end;
    pattern fun (v_3231 : Mem) (v_3232 : reg (bv 128)) => do
      v_15040 <- getRegister v_3232;
      v_15042 <- evaluateAddress v_3231;
      v_15043 <- load v_15042 16;
      setRegister (lhs.of_reg v_3232) (concat (sub (extract v_15040 0 16) (extract v_15043 0 16)) (concat (sub (extract v_15040 16 32) (extract v_15043 16 32)) (concat (sub (extract v_15040 32 48) (extract v_15043 32 48)) (concat (sub (extract v_15040 48 64) (extract v_15043 48 64)) (concat (sub (extract v_15040 64 80) (extract v_15043 64 80)) (concat (sub (extract v_15040 80 96) (extract v_15043 80 96)) (concat (sub (extract v_15040 96 112) (extract v_15043 96 112)) (sub (extract v_15040 112 128) (extract v_15043 112 128)))))))));
      pure ()
    pat_end
