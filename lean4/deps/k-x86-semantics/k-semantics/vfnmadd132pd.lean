def vfnmadd132pd1 : instruction :=
  definst "vfnmadd132pd" $ do
    pattern fun (v_3167 : reg (bv 128)) (v_3168 : reg (bv 128)) (v_3169 : reg (bv 128)) => do
      v_6868 <- getRegister v_3169;
      v_6870 <- getRegister v_3168;
      v_6872 <- getRegister v_3167;
      setRegister (lhs.of_reg v_3169) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6868 0 64) (extract v_6870 0 64) (extract v_6872 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6868 64 128) (extract v_6870 64 128) (extract v_6872 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3181 : reg (bv 256)) (v_3182 : reg (bv 256)) (v_3183 : reg (bv 256)) => do
      v_6886 <- getRegister v_3183;
      v_6888 <- getRegister v_3182;
      v_6890 <- getRegister v_3181;
      setRegister (lhs.of_reg v_3183) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6886 0 64) (extract v_6888 0 64) (extract v_6890 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6886 64 128) (extract v_6888 64 128) (extract v_6890 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6886 128 192) (extract v_6888 128 192) (extract v_6890 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_6886 192 256) (extract v_6888 192 256) (extract v_6890 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3164 : Mem) (v_3162 : reg (bv 128)) (v_3163 : reg (bv 128)) => do
      v_12650 <- getRegister v_3163;
      v_12652 <- getRegister v_3162;
      v_12654 <- evaluateAddress v_3164;
      v_12655 <- load v_12654 16;
      setRegister (lhs.of_reg v_3163) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12650 0 64) (extract v_12652 0 64) (extract v_12655 0 64)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12650 64 128) (extract v_12652 64 128) (extract v_12655 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3173 : Mem) (v_3176 : reg (bv 256)) (v_3177 : reg (bv 256)) => do
      v_12664 <- getRegister v_3177;
      v_12666 <- getRegister v_3176;
      v_12668 <- evaluateAddress v_3173;
      v_12669 <- load v_12668 32;
      setRegister (lhs.of_reg v_3177) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12664 0 64) (extract v_12666 0 64) (extract v_12669 0 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12664 64 128) (extract v_12666 64 128) (extract v_12669 64 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12664 128 192) (extract v_12666 128 192) (extract v_12669 128 192)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_double (extract v_12664 192 256) (extract v_12666 192 256) (extract v_12669 192 256)))));
      pure ()
    pat_end
