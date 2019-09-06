def pmulld1 : instruction :=
  definst "pmulld" $ do
    pattern fun (v_2901 : reg (bv 128)) (v_2902 : reg (bv 128)) => do
      v_5871 <- getRegister v_2902;
      v_5874 <- getRegister v_2901;
      setRegister (lhs.of_reg v_2902) (concat (extract (mul (sext (extract v_5871 0 32) 64) (sext (extract v_5874 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_5871 32 64) 64) (sext (extract v_5874 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_5871 64 96) 64) (sext (extract v_5874 64 96) 64)) 32 64) (extract (mul (sext (extract v_5871 96 128) 64) (sext (extract v_5874 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2897 : Mem) (v_2898 : reg (bv 128)) => do
      v_12572 <- getRegister v_2898;
      v_12575 <- evaluateAddress v_2897;
      v_12576 <- load v_12575 16;
      setRegister (lhs.of_reg v_2898) (concat (extract (mul (sext (extract v_12572 0 32) 64) (sext (extract v_12576 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_12572 32 64) 64) (sext (extract v_12576 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_12572 64 96) 64) (sext (extract v_12576 64 96) 64)) 32 64) (extract (mul (sext (extract v_12572 96 128) 64) (sext (extract v_12576 96 128) 64)) 32 64))));
      pure ()
    pat_end
