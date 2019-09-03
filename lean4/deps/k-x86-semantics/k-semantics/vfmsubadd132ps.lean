def vfmsubadd132ps1 : instruction :=
  definst "vfmsubadd132ps" $ do
    pattern fun (v_2981 : reg (bv 128)) (v_2982 : reg (bv 128)) (v_2983 : reg (bv 128)) => do
      v_9124 <- getRegister v_2983;
      v_9125 <- eval (extract v_9124 0 32);
      v_9133 <- getRegister v_2981;
      v_9134 <- eval (extract v_9133 0 32);
      v_9143 <- getRegister v_2982;
      v_9144 <- eval (extract v_9143 0 32);
      v_9154 <- eval (extract v_9124 32 64);
      v_9162 <- eval (extract v_9133 32 64);
      v_9171 <- eval (extract v_9143 32 64);
      v_9182 <- eval (extract v_9124 64 96);
      v_9190 <- eval (extract v_9133 64 96);
      v_9199 <- eval (extract v_9143 64 96);
      v_9209 <- eval (extract v_9124 96 128);
      v_9217 <- eval (extract v_9133 96 128);
      v_9226 <- eval (extract v_9143 96 128);
      setRegister (lhs.of_reg v_2983) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9125 0 1)) (uvalueMInt (extract v_9125 1 9)) (uvalueMInt (extract v_9125 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9134 0 1)) (uvalueMInt (extract v_9134 1 9)) (uvalueMInt (extract v_9134 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9144 0 1)) (uvalueMInt (extract v_9144 1 9)) (uvalueMInt (extract v_9144 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9154 0 1)) (uvalueMInt (extract v_9154 1 9)) (uvalueMInt (extract v_9154 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9162 0 1)) (uvalueMInt (extract v_9162 1 9)) (uvalueMInt (extract v_9162 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9171 0 1)) (uvalueMInt (extract v_9171 1 9)) (uvalueMInt (extract v_9171 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9182 0 1)) (uvalueMInt (extract v_9182 1 9)) (uvalueMInt (extract v_9182 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9190 0 1)) (uvalueMInt (extract v_9190 1 9)) (uvalueMInt (extract v_9190 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9199 0 1)) (uvalueMInt (extract v_9199 1 9)) (uvalueMInt (extract v_9199 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9209 0 1)) (uvalueMInt (extract v_9209 1 9)) (uvalueMInt (extract v_9209 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9217 0 1)) (uvalueMInt (extract v_9217 1 9)) (uvalueMInt (extract v_9217 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9226 0 1)) (uvalueMInt (extract v_9226 1 9)) (uvalueMInt (extract v_9226 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2992 : reg (bv 256)) (v_2993 : reg (bv 256)) (v_2994 : reg (bv 256)) => do
      v_9244 <- getRegister v_2994;
      v_9245 <- eval (extract v_9244 0 32);
      v_9253 <- getRegister v_2992;
      v_9254 <- eval (extract v_9253 0 32);
      v_9263 <- getRegister v_2993;
      v_9264 <- eval (extract v_9263 0 32);
      v_9274 <- eval (extract v_9244 32 64);
      v_9282 <- eval (extract v_9253 32 64);
      v_9291 <- eval (extract v_9263 32 64);
      v_9302 <- eval (extract v_9244 64 96);
      v_9310 <- eval (extract v_9253 64 96);
      v_9319 <- eval (extract v_9263 64 96);
      v_9329 <- eval (extract v_9244 96 128);
      v_9337 <- eval (extract v_9253 96 128);
      v_9346 <- eval (extract v_9263 96 128);
      v_9357 <- eval (extract v_9244 128 160);
      v_9365 <- eval (extract v_9253 128 160);
      v_9374 <- eval (extract v_9263 128 160);
      v_9384 <- eval (extract v_9244 160 192);
      v_9392 <- eval (extract v_9253 160 192);
      v_9401 <- eval (extract v_9263 160 192);
      v_9412 <- eval (extract v_9244 192 224);
      v_9420 <- eval (extract v_9253 192 224);
      v_9429 <- eval (extract v_9263 192 224);
      v_9439 <- eval (extract v_9244 224 256);
      v_9447 <- eval (extract v_9253 224 256);
      v_9456 <- eval (extract v_9263 224 256);
      setRegister (lhs.of_reg v_2994) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9245 0 1)) (uvalueMInt (extract v_9245 1 9)) (uvalueMInt (extract v_9245 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9254 0 1)) (uvalueMInt (extract v_9254 1 9)) (uvalueMInt (extract v_9254 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9264 0 1)) (uvalueMInt (extract v_9264 1 9)) (uvalueMInt (extract v_9264 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9274 0 1)) (uvalueMInt (extract v_9274 1 9)) (uvalueMInt (extract v_9274 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9282 0 1)) (uvalueMInt (extract v_9282 1 9)) (uvalueMInt (extract v_9282 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9291 0 1)) (uvalueMInt (extract v_9291 1 9)) (uvalueMInt (extract v_9291 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9302 0 1)) (uvalueMInt (extract v_9302 1 9)) (uvalueMInt (extract v_9302 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9310 0 1)) (uvalueMInt (extract v_9310 1 9)) (uvalueMInt (extract v_9310 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9319 0 1)) (uvalueMInt (extract v_9319 1 9)) (uvalueMInt (extract v_9319 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9329 0 1)) (uvalueMInt (extract v_9329 1 9)) (uvalueMInt (extract v_9329 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9337 0 1)) (uvalueMInt (extract v_9337 1 9)) (uvalueMInt (extract v_9337 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9346 0 1)) (uvalueMInt (extract v_9346 1 9)) (uvalueMInt (extract v_9346 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9357 0 1)) (uvalueMInt (extract v_9357 1 9)) (uvalueMInt (extract v_9357 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9365 0 1)) (uvalueMInt (extract v_9365 1 9)) (uvalueMInt (extract v_9365 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9374 0 1)) (uvalueMInt (extract v_9374 1 9)) (uvalueMInt (extract v_9374 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9384 0 1)) (uvalueMInt (extract v_9384 1 9)) (uvalueMInt (extract v_9384 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9392 0 1)) (uvalueMInt (extract v_9392 1 9)) (uvalueMInt (extract v_9392 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9401 0 1)) (uvalueMInt (extract v_9401 1 9)) (uvalueMInt (extract v_9401 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9412 0 1)) (uvalueMInt (extract v_9412 1 9)) (uvalueMInt (extract v_9412 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9420 0 1)) (uvalueMInt (extract v_9420 1 9)) (uvalueMInt (extract v_9420 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9429 0 1)) (uvalueMInt (extract v_9429 1 9)) (uvalueMInt (extract v_9429 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9439 0 1)) (uvalueMInt (extract v_9439 1 9)) (uvalueMInt (extract v_9439 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9447 0 1)) (uvalueMInt (extract v_9447 1 9)) (uvalueMInt (extract v_9447 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9456 0 1)) (uvalueMInt (extract v_9456 1 9)) (uvalueMInt (extract v_9456 9 32)))) 32)))));
      pure ()
    pat_end;
    pattern fun (v_2978 : Mem) (v_2976 : reg (bv 128)) (v_2977 : reg (bv 128)) => do
      v_19861 <- getRegister v_2977;
      v_19862 <- eval (extract v_19861 0 32);
      v_19870 <- evaluateAddress v_2978;
      v_19871 <- load v_19870 16;
      v_19872 <- eval (extract v_19871 0 32);
      v_19881 <- getRegister v_2976;
      v_19882 <- eval (extract v_19881 0 32);
      v_19892 <- eval (extract v_19861 32 64);
      v_19900 <- eval (extract v_19871 32 64);
      v_19909 <- eval (extract v_19881 32 64);
      v_19920 <- eval (extract v_19861 64 96);
      v_19928 <- eval (extract v_19871 64 96);
      v_19937 <- eval (extract v_19881 64 96);
      v_19947 <- eval (extract v_19861 96 128);
      v_19955 <- eval (extract v_19871 96 128);
      v_19964 <- eval (extract v_19881 96 128);
      setRegister (lhs.of_reg v_2977) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19862 0 1)) (uvalueMInt (extract v_19862 1 9)) (uvalueMInt (extract v_19862 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19872 0 1)) (uvalueMInt (extract v_19872 1 9)) (uvalueMInt (extract v_19872 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19882 0 1)) (uvalueMInt (extract v_19882 1 9)) (uvalueMInt (extract v_19882 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19892 0 1)) (uvalueMInt (extract v_19892 1 9)) (uvalueMInt (extract v_19892 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19900 0 1)) (uvalueMInt (extract v_19900 1 9)) (uvalueMInt (extract v_19900 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19909 0 1)) (uvalueMInt (extract v_19909 1 9)) (uvalueMInt (extract v_19909 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19920 0 1)) (uvalueMInt (extract v_19920 1 9)) (uvalueMInt (extract v_19920 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19928 0 1)) (uvalueMInt (extract v_19928 1 9)) (uvalueMInt (extract v_19928 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19937 0 1)) (uvalueMInt (extract v_19937 1 9)) (uvalueMInt (extract v_19937 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19947 0 1)) (uvalueMInt (extract v_19947 1 9)) (uvalueMInt (extract v_19947 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19955 0 1)) (uvalueMInt (extract v_19955 1 9)) (uvalueMInt (extract v_19955 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19964 0 1)) (uvalueMInt (extract v_19964 1 9)) (uvalueMInt (extract v_19964 9 32)))) 32)));
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) (v_2988 : reg (bv 256)) (v_2989 : reg (bv 256)) => do
      v_19977 <- getRegister v_2989;
      v_19978 <- eval (extract v_19977 0 32);
      v_19986 <- evaluateAddress v_2987;
      v_19987 <- load v_19986 32;
      v_19988 <- eval (extract v_19987 0 32);
      v_19997 <- getRegister v_2988;
      v_19998 <- eval (extract v_19997 0 32);
      v_20008 <- eval (extract v_19977 32 64);
      v_20016 <- eval (extract v_19987 32 64);
      v_20025 <- eval (extract v_19997 32 64);
      v_20036 <- eval (extract v_19977 64 96);
      v_20044 <- eval (extract v_19987 64 96);
      v_20053 <- eval (extract v_19997 64 96);
      v_20063 <- eval (extract v_19977 96 128);
      v_20071 <- eval (extract v_19987 96 128);
      v_20080 <- eval (extract v_19997 96 128);
      v_20091 <- eval (extract v_19977 128 160);
      v_20099 <- eval (extract v_19987 128 160);
      v_20108 <- eval (extract v_19997 128 160);
      v_20118 <- eval (extract v_19977 160 192);
      v_20126 <- eval (extract v_19987 160 192);
      v_20135 <- eval (extract v_19997 160 192);
      v_20146 <- eval (extract v_19977 192 224);
      v_20154 <- eval (extract v_19987 192 224);
      v_20163 <- eval (extract v_19997 192 224);
      v_20173 <- eval (extract v_19977 224 256);
      v_20181 <- eval (extract v_19987 224 256);
      v_20190 <- eval (extract v_19997 224 256);
      setRegister (lhs.of_reg v_2989) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19978 0 1)) (uvalueMInt (extract v_19978 1 9)) (uvalueMInt (extract v_19978 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19988 0 1)) (uvalueMInt (extract v_19988 1 9)) (uvalueMInt (extract v_19988 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_19998 0 1)) (uvalueMInt (extract v_19998 1 9)) (uvalueMInt (extract v_19998 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20008 0 1)) (uvalueMInt (extract v_20008 1 9)) (uvalueMInt (extract v_20008 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20016 0 1)) (uvalueMInt (extract v_20016 1 9)) (uvalueMInt (extract v_20016 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20025 0 1)) (uvalueMInt (extract v_20025 1 9)) (uvalueMInt (extract v_20025 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20036 0 1)) (uvalueMInt (extract v_20036 1 9)) (uvalueMInt (extract v_20036 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20044 0 1)) (uvalueMInt (extract v_20044 1 9)) (uvalueMInt (extract v_20044 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20053 0 1)) (uvalueMInt (extract v_20053 1 9)) (uvalueMInt (extract v_20053 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20063 0 1)) (uvalueMInt (extract v_20063 1 9)) (uvalueMInt (extract v_20063 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20071 0 1)) (uvalueMInt (extract v_20071 1 9)) (uvalueMInt (extract v_20071 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20080 0 1)) (uvalueMInt (extract v_20080 1 9)) (uvalueMInt (extract v_20080 9 32)))) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20091 0 1)) (uvalueMInt (extract v_20091 1 9)) (uvalueMInt (extract v_20091 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20099 0 1)) (uvalueMInt (extract v_20099 1 9)) (uvalueMInt (extract v_20099 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20108 0 1)) (uvalueMInt (extract v_20108 1 9)) (uvalueMInt (extract v_20108 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20118 0 1)) (uvalueMInt (extract v_20118 1 9)) (uvalueMInt (extract v_20118 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20126 0 1)) (uvalueMInt (extract v_20126 1 9)) (uvalueMInt (extract v_20126 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20135 0 1)) (uvalueMInt (extract v_20135 1 9)) (uvalueMInt (extract v_20135 9 32)))) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20146 0 1)) (uvalueMInt (extract v_20146 1 9)) (uvalueMInt (extract v_20146 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20154 0 1)) (uvalueMInt (extract v_20154 1 9)) (uvalueMInt (extract v_20154 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20163 0 1)) (uvalueMInt (extract v_20163 1 9)) (uvalueMInt (extract v_20163 9 32)))) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20173 0 1)) (uvalueMInt (extract v_20173 1 9)) (uvalueMInt (extract v_20173 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20181 0 1)) (uvalueMInt (extract v_20181 1 9)) (uvalueMInt (extract v_20181 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_20190 0 1)) (uvalueMInt (extract v_20190 1 9)) (uvalueMInt (extract v_20190 9 32)))) 32)))));
      pure ()
    pat_end
